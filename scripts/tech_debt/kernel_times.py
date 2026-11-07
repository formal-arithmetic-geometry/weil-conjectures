#!/usr/bin/env python3
"""Declarations that are slow to type-check in the kernel.

Drives `KernelTimes.lean`, which re-sends a built module's declarations through the kernel
(one `lean --run` process per module; it needs a built tree and builds nothing), and keeps the
results in a sorted TSV table:

  # kernel-times	rev=<commit>	threshold_ms=<T>	level=<exported|private>
  DECL	<ms>	<module>	<declaration>      kernel calls of at least T ms
  MODULE	<module>	<kernel ms>	<kernel calls>	<import ms>
  ERROR	<module>	<message>

Commands:
  kernel_times.py measure --out TABLE [--all | --since REV] [--previous TABLE] [--jobs N]
                          [--threshold-ms T] [--timeout S] [--level exported|private]
  kernel_times.py report TABLE [--previous TABLE] [--top N] [--repo-url URL]

`measure --since REV` measures only the modules whose source changed between REV and HEAD and
carries every other module's rows over from `--previous` (the daily mode); `--all` measures every
module. Cost per module: loading its imports (5-30 s, 5-10 GB of RAM including the mapped
`.olean` files) plus its kernel time.
"""

import argparse
import concurrent.futures
import os
import shlex
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN_SCRIPT = os.path.join(HERE, "KernelTimes.lean")

# Source directories of the measured libraries (lakefile.toml): module name = path below them.
SRC_DIRS = [("WeilConjectures/", ""), ("Comparator/Weil/", "Comparator/"),
            ("Comparator/LeanEvalWeil/", "Comparator/")]


def git(*args):
    return subprocess.run(["git", *args], check=True, stdout=subprocess.PIPE).stdout.decode()


def module_of(path):
    if not path.endswith(".lean"):
        return None
    for prefix, src_dir in SRC_DIRS:
        if path.startswith(prefix):
            return path[len(src_dir):-len(".lean")].replace("/", ".")
    return None


def modules_at_head():
    return sorted({m for p in git("ls-files", "-z").split("\0") if (m := module_of(p))})


def changed_modules(since):
    paths = git("diff", "-z", "--name-only", "--no-renames", since, "HEAD").split("\0")
    return {m for p in paths if (m := module_of(p))}


# ---------------------------------------------------------------------------------------------
# The table

class Table:
    def __init__(self):
        self.meta = {}
        self.decls = {}    # (module, name) -> ms
        self.modules = {}  # module -> (kernel ms, kernel calls, import ms)
        self.errors = {}   # module -> message

    @staticmethod
    def load(path):
        t = Table()
        with open(path, encoding="utf-8") as f:
            for line in f:
                fields = line.rstrip("\n").split("\t")
                if fields[0] == "# kernel-times":
                    t.meta = dict(kv.split("=", 1) for kv in fields[1:])
                elif fields[0] == "DECL":
                    t.decls[(fields[2], fields[3])] = int(fields[1])
                elif fields[0] == "MODULE":
                    t.modules[fields[1]] = tuple(int(x) for x in fields[2:5])
                elif fields[0] == "ERROR":
                    t.errors[fields[1]] = fields[2] if len(fields) > 2 else ""
        return t

    def add_output(self, module, out):
        """Parse the output of `KernelTimes.lean` for one module."""
        for line in out.splitlines():
            fields = line.split("\t")
            if fields[0] == "DECL" and len(fields) == 4:
                self.decls[(fields[2], fields[3])] = int(fields[1])
            elif fields[0] == "MODULE" and len(fields) == 5:
                self.modules[fields[1]] = tuple(int(x) for x in fields[2:5])
            elif fields[0] == "ERROR" and len(fields) >= 3:
                self.errors[fields[1]] = fields[2][:500]
        if module not in self.modules and module not in self.errors:
            self.errors[module] = "no result"

    def drop_modules(self, mods):
        mods = set(mods)
        self.decls = {k: v for k, v in self.decls.items() if k[0] not in mods}
        self.modules = {k: v for k, v in self.modules.items() if k not in mods}
        self.errors = {k: v for k, v in self.errors.items() if k not in mods}

    def save(self, path):
        with open(path, "w", encoding="utf-8") as f:
            f.write("\t".join(["# kernel-times"] + [f"{k}={v}" for k, v in sorted(self.meta.items())]) + "\n")
            for (mod, name), ms in sorted(self.decls.items()):
                f.write(f"DECL\t{ms}\t{mod}\t{name}\n")
            for mod, (k, n, i) in sorted(self.modules.items()):
                f.write(f"MODULE\t{mod}\t{k}\t{n}\t{i}\n")
            for mod, msg in sorted(self.errors.items()):
                f.write(f"ERROR\t{mod}\t{msg}\n")


# ---------------------------------------------------------------------------------------------
# measure

def run_module(mod, args):
    cmd = [*shlex.split(args.lean), "--run", LEAN_SCRIPT, "--threshold-ms", str(args.threshold_ms),
           "--level", args.level, mod]
    start = time.monotonic()
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=args.timeout)
        out = p.stdout.decode("utf-8", "replace")
        if p.returncode != 0 and "ERROR\t" not in out:
            err = p.stderr.decode("utf-8", "replace").strip().replace("\n", " ")
            out += f"\nERROR\t{mod}\texit {p.returncode}: {err[-300:]}"
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"").decode("utf-8", "replace")
        out += f"\nERROR\t{mod}\ttimeout after {args.timeout} s"
    return mod, out, time.monotonic() - start


def cmd_measure(args):
    head = git("rev-parse", "HEAD").strip()
    all_mods = modules_at_head()
    table = Table.load(args.previous) if args.previous and os.path.exists(args.previous) else Table()
    # A table measured with other settings cannot be extended.
    if (table.meta.get("threshold_ms"), table.meta.get("level")) != (str(args.threshold_ms), args.level):
        table = Table()
    if args.all or not args.since:
        todo = all_mods
        table = Table()
    else:
        todo = sorted(changed_modules(args.since) & set(all_mods))
    # Keep the rows of unchanged modules that still exist; re-measure the rest.
    table.drop_modules((set(table.modules) | set(table.errors)) - set(all_mods))
    table.drop_modules(todo)
    table.meta = {"rev": head, "threshold_ms": str(args.threshold_ms), "level": args.level,
                  "measured": str(len(todo)), "modules": str(len(all_mods))}
    print(f"measuring {len(todo)} of {len(all_mods)} modules with {args.jobs} jobs", file=sys.stderr)
    start = time.monotonic()
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        for i, (mod, out, secs) in enumerate(pool.map(lambda m: run_module(m, args), todo), 1):
            table.add_output(mod, out)
            print(f"[{i}/{len(todo)}] {mod} {secs:.1f} s", file=sys.stderr)
    table.save(args.out)
    print(f"done in {time.monotonic() - start:.0f} s", file=sys.stderr)


# ---------------------------------------------------------------------------------------------
# report

def fmt_ms(ms):
    return f"{ms / 1000:.1f} s"


def display(mod, name):
    """`_private.<module>.0.foo` as `foo (private)`."""
    prefix = f"_private.{mod}.0."
    return f"`{name[len(prefix):]}` (private)" if name.startswith(prefix) else f"`{name}`"


def cmd_report(args):
    cur = Table.load(args.table)
    prev = Table.load(args.previous) if args.previous and os.path.exists(args.previous) else None
    url = args.repo_url
    rev = cur.meta.get("rev", "?")
    link = f"[`{rev[:10]}`]({url}/commit/{rev})" if url else f"`{rev[:10]}`"
    thr = int(cur.meta.get("threshold_ms", "1000"))
    lines = [f"**Kernel type-checking** at {link} ({cur.meta.get('level', 'exported')} imports; "
             f"{cur.meta.get('measured', '?')} of {cur.meta.get('modules', '?')} modules measured "
             f"in this run, the others carried over)."]

    def stats(t):
        return {
            f"declarations ≥ {fmt_ms(thr)}": sum(1 for v in t.decls.values() if v >= thr),
            "declarations ≥ 10 s": sum(1 for v in t.decls.values() if v >= 10000),
            "declarations ≥ 60 s": sum(1 for v in t.decls.values() if v >= 60000),
            "total kernel time (s)": sum(k for k, _, _ in t.modules.values()) // 1000,
            "modules with results": len(t.modules),
            "modules that failed": len(t.errors),
        }
    s = stats(cur)
    ps = stats(prev) if prev else {}
    lines += ["", "| | Now | Change |", "|:-|-:|-:|"]
    for k, v in s.items():
        d = v - ps[k] if k in ps else None
        lines.append(f"| {k} | {v} | {'' if d is None else (f'+{d}' if d > 0 else d)} |")
    top = sorted(cur.decls.items(), key=lambda kv: (-kv[1], kv[0]))[:args.top]
    if top:
        lines += ["", f"Slowest {len(top)} declarations:", "", "| Time | Declaration | Module | Before |",
                  "|-:|:-|:-|-:|"]
        for (mod, name), ms in top:
            before = "" if prev is None else (fmt_ms(prev.decls[(mod, name)]) if (mod, name) in prev.decls else "new")
            lines.append(f"| {fmt_ms(ms)} | {display(mod, name)} | `{mod}` | {before} |")
    if prev is not None:
        shown = {k for k, _ in top}
        new = sorted(((k, v) for k, v in cur.decls.items()
                      if k not in shown and (k not in prev.decls or v >= 2 * prev.decls[k] + thr)),
                     key=lambda kv: -kv[1])
        if new:
            lines += ["", f"Further declarations that are new or ≥ 2× slower since the previous report ({len(new)}):", ""]
            for (mod, name), ms in new[:args.top]:
                was = f", was {fmt_ms(prev.decls[(mod, name)])}" if (mod, name) in prev.decls else ""
                lines.append(f"- {display(mod, name)} ({fmt_ms(ms)}{was}) in `{mod}`")
    if cur.errors:
        lines += ["", f"Failed modules ({len(cur.errors)}): " +
                  ", ".join(f"`{m}`" for m in sorted(cur.errors)[:20]) + (" ..." if len(cur.errors) > 20 else "")]
    print("\n".join(lines))


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    m = sub.add_parser("measure")
    m.add_argument("--out", required=True)
    m.add_argument("--all", action="store_true", help="measure every module")
    m.add_argument("--since", help="measure the modules changed since this commit")
    m.add_argument("--previous", help="table whose rows are kept for unchanged modules")
    m.add_argument("--jobs", type=int, default=8)
    m.add_argument("--threshold-ms", type=int, default=1000)
    m.add_argument("--timeout", type=int, default=1800, help="seconds per module")
    m.add_argument("--level", choices=["exported", "private"], default="exported")
    m.add_argument("--lean", default="lake env lean", help="command that runs Lean in the built tree")
    r = sub.add_parser("report")
    r.add_argument("table")
    r.add_argument("--previous")
    r.add_argument("--top", type=int, default=15)
    r.add_argument("--repo-url")
    args = p.parse_args()
    (cmd_measure if args.cmd == "measure" else cmd_report)(args)


if __name__ == "__main__":
    main()
