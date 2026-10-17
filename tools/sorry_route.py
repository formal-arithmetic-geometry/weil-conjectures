#!/usr/bin/env python3
"""Sorry route of the open targets (launcher, 2026-10-16; plain scratch files 2026-10-17), written to
local/sorry-route.json.

For each open batch N (coord/batchN-targets.txt without coord/batchN-complete.txt, every N present) and each target
module listed there, a scratch file is compiled through tools/lean_file.sh that imports that one module and walks the
constants its declarations use, transitively through types and values (tools/sorry_route.lean, `sorryRoute`). The
project declarations (roots Sheaf, WeilConjectures) on that walk whose own term contains `sorryAx` are the stage-3 work
of the batch; a sorry the targets import but do not use is not on the route.

The scratch file is a plain Lean file, not a `module`: a `module` file sees neither the private part nor the
non-exposed bodies of what it imports, so the walk found nothing and printed nothing (sorry-route.json was empty from
2026-10-16 to 2026-10-17 and the batch tags fell back to the import closure). A plain file imports the full .olean.

Output: {"t", "ok", "failed": [target modules whose walk failed], "route": {module: [declarations]} (union over the open
batches), "batches": {batchN: {module: [declarations]}}, "targets": {target module: {module: [declarations]}}}.
`ok` is false when any target module failed: consumers must not read a partial route as complete (tools/tag_batches.py
then keeps the import closure for that batch and says so). Exit 1 when a walk failed.
Usage: tools/sorry_route.py [N ...]      (default: every open batch; the file always describes the batches it lists)"""
import json, os, pathlib, re, subprocess, sys, time
R = pathlib.Path(__file__).resolve().parent.parent
SB = R / "lean" / ".sandbox" / "_sheaf"; SB.mkdir(parents=True, exist_ok=True)
LIB = (R / "tools" / "sorry_route.lean").read_text()
body = LIB[LIB.index("open Lean Meta"):]


def open_batches():
    ns = sorted(int(m.group(1)) for p in (R / "coord").glob("batch*-targets.txt")
                if (m := re.fullmatch(r"batch(\d+)-targets\.txt", p.name)))
    return [n for n in ns if not (R / f"coord/batch{n}-complete.txt").exists()]


def targets(n):
    p = R / f"coord/batch{n}-targets.txt"
    return [l.strip() for l in p.read_text().splitlines() if l.strip() and not l.startswith("#")]


DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|public|unsafe|partial)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\b", re.M)
IMP = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(\S+)", re.M)


def declaring(mod, depth=0):
    """The modules whose declarations are the targets of `mod`: `mod` itself, or, for a target module that only
    re-exports (Sheaf.Targets.EtaleSmooth is `public import WeilConjectures...Smooth`), the project modules it imports."""
    p = R / "lean" / (mod.replace(".", "/") + ".lean")
    text = p.read_text(errors="ignore") if p.is_file() else ""
    if DECL.search(text) or depth > 2:
        return [mod]
    out = []
    for i in IMP.findall(text):
        if i.split(".")[0] in ("Sheaf", "WeilConjectures"):
            out += declaring(i, depth + 1)
    return out or [mod]


def walk(mod):
    """{module: set(declarations)} of the sorried project declarations the declarations of `mod` use; None on failure."""
    f = SB / f"SorryRoute_{mod.replace('.', '_')}.lean"
    mods = declaring(mod)
    names = ", ".join(f"`{m}" for m in mods)
    f.write_text(f"import Lean\nimport {mod}\n{body}\n#eval show MetaM Unit from do\n"
                 f"  let env ← getEnv\n"
                 f"  let mis := [{names}].filterMap env.getModuleIdx?\n"
                 f"  if mis.length != {len(mods)} then throwError \"target modules not loaded\"\n"
                 f"  let decls := env.constants.map₁.toList.filterMap fun (n, _) =>\n"
                 f"    if (env.getModuleIdxFor? n).any mis.contains && !n.isInternalDetail then some n else none\n"
                 f"  IO.println s!\"TARGETDECLS {{decls.length}}\"\n"
                 f"  for (d, m) in (← sorryRoute decls) do IO.println s!\"ROUTE {{m}} {{d}}\"\n")
    env = dict(os.environ, SHEAF_FILE_TIMEOUT="900")
    r = subprocess.run(["tools/lean_file.sh", str(f.relative_to(R))], cwd=R, env=env, capture_output=True, text=True,
                       timeout=1200)
    out = r.stdout + r.stderr
    nd = re.search(r"^TARGETDECLS (\d+)$", out, re.M)
    if r.returncode or not nd or int(nd.group(1)) == 0:
        print(f"{mod}: walk failed (rc {r.returncode}): " + out.strip()[-600:], file=sys.stderr)
        return None
    f.unlink(missing_ok=True)
    res = {}
    for m, d in re.findall(r"^ROUTE (\S+) (\S+)$", out, re.M):
        res.setdefault(m, set()).add(d)
    return res


def load():
    """The route as consumers read it: None when local/sorry-route.json is missing, unreadable or not `ok` (a failed
    walk: the caller keeps the import closure and says so); else {"t", "batches": {batchN: set(modules)}, "route": set}."""
    try:
        d = json.loads((R / "local" / "sorry-route.json").read_text())
    except (OSError, ValueError):
        return None
    if not d.get("ok") or "batches" not in d:
        return None
    return {"t": d["t"], "batches": {k: set(v) for k, v in d["batches"].items()}, "route": set(d["route"])}


def changed_since(t, modules):
    """Modules whose source changed after the route was computed: a landing may have added a sorry the route does not
    know yet (a split); consumers keep them until the next refresh (~/cc1/sorry-route-loop.sh after each green build)."""
    out = set()
    for m in modules:
        p = R / "lean" / (m.replace(".", "/") + ".lean")
        try:
            if p.stat().st_mtime > t: out.add(m)
        except OSError:
            pass
    return out


def main():
    ns = [int(a) for a in sys.argv[1:]] or open_batches()
    route, batches, tgt, failed = {}, {}, {}, []
    for n in ns:
        b = batches.setdefault(f"batch{n}", {})
        for mod in targets(n):
            if mod not in tgt:
                w = walk(mod)
                if w is None:
                    failed.append(mod); continue
                tgt[mod] = w
            for m, ds in tgt[mod].items():
                b.setdefault(m, set()).update(ds); route.setdefault(m, set()).update(ds)
    srt = lambda d: {m: sorted(v) for m, v in sorted(d.items())}  # noqa: E731
    out = {"t": time.time(), "ok": not failed, "failed": failed, "route": srt(route),
           "batches": {k: srt(v) for k, v in batches.items()}, "targets": {k: srt(v) for k, v in tgt.items()}}
    (R / "local").mkdir(exist_ok=True)
    tmp = R / "local" / ".sorry-route.json"; tmp.write_text(json.dumps(out, indent=1)); tmp.replace(R / "local" / "sorry-route.json")
    for k, v in out["batches"].items():
        print(f"{k}: {sum(len(x) for x in v.values())} sorried declarations in {len(v)} modules")
    print(len(route), "modules on the sorry route;", "failed:", failed)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
