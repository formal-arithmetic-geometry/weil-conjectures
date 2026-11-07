#!/usr/bin/env python3
"""Technical-debt counters for the Lean sources (the analogue of Mathlib's
`technical-debt-metrics.py`, in leanprover-community/mathlib-ci `scripts/reporting/`).

Counted in `WeilConjectures/` and `Comparator/` (`.lean` files), after removing comments and
string literals, so that prose such as "the sheaf axiom" or "admit a lift" does not count:

* linter suppressions: `set_option linter.X false` (per linter; `... in` and file/section-wide
  forms are also totalled separately) and `@[nolint X]` (per linter);
* heartbeat and limit modifications: `maxHeartbeats`, `synthInstance.maxHeartbeats`,
  `maxRecDepth`, `synthInstance.maxSize`, each split into raised / unlimited (0) /
  lowered (below Lean's default) / reset to the default;
* backward-compatibility options (`set_option backward.* ...`, per option), which Mathlib
  counts as "strong" technical debt;
* `sorry`, `admit`, `axiom` declarations, `@[deprecated]`, `erw`, `#adaptation_note`.

Mathlib's porting notes do not exist here and are not counted.

Usage:
  metrics.py count [--rev REV] [--format table|tsv|json] [--per-file]
  metrics.py diff BASE HEAD [--format markdown|table|tsv] [--max-files N] [--repo-url URL]
                  [--flavor github|zulip] [--full]

`--rev` reads the files of a commit from the object database (`git cat-file`), without a
checkout; without it, the working tree's tracked files are read. In `diff`, BASE and HEAD are
commits or JSON files written by `count --format json`. Given two commits, only HEAD is counted
in full; BASE is HEAD minus the changes in the files that differ. The script only reads
files: it is safe to run on an untrusted tree.

All output is sorted, so that two outputs can be compared with `diff`.
"""

import argparse
import json
import os
import re
import subprocess
import sys
from collections import Counter

ROOTS = ("WeilConjectures/", "Comparator/")

# Lean's defaults (Lean 4.33.1: `maxHeartbeats` in Lean/CoreM.lean, the `synthInstance.*`
# options in Lean/Meta/SynthInstance.lean, `defaultMaxRecDepth` in Init/Prelude.lean).
LIMIT_DEFAULTS = {
    "maxHeartbeats": 200000,
    "synthInstance.maxHeartbeats": 20000,
    "maxRecDepth": 512,
    "synthInstance.maxSize": 128,
}

# Category names, in report order.
LINTER = "linter suppressions"
LINTER_SCOPE = "linter suppressions by scope"
LIMITS = "heartbeat and limit modifications"
BACKWARD = "backward-compatibility options"
OTHER = "other"
CATEGORIES = [OTHER, LINTER, LINTER_SCOPE, LIMITS, BACKWARD]

# ---------------------------------------------------------------------------------------------
# Removing comments and strings

_TOKEN = re.compile(r"/-|--|\"|'(?:\\.|[^\\'\n])'")
_BLOCK = re.compile(r"/-|-/")
_STRING = re.compile(r'"(?:\\.|[^"\\])*"', re.S)


def strip_comments(src):
    """Return `src` with comments (nested `/- -/`, `--`) and string literals blanked out.

    Newlines inside removed text are kept, so that `^`-anchored patterns stay meaningful.
    Character literals such as `'"'` are kept as code.
    """
    out = []
    i, n = 0, len(src)
    while i < n:
        m = _TOKEN.search(src, i)
        if not m:
            out.append(src[i:])
            break
        out.append(src[i:m.start()])
        tok = m.group()
        if tok == "--":
            j = src.find("\n", m.end())
            i = n if j < 0 else j
        elif tok == "/-":
            depth, j = 1, m.end()
            while depth:
                b = _BLOCK.search(src, j)
                if not b:
                    j = n
                    break
                depth += 1 if b.group() == "/-" else -1
                j = b.end()
            out.append("\n" * src.count("\n", m.start(), j))
            i = j
        elif tok == '"':
            s = _STRING.match(src, m.start())
            j = s.end() if s else n
            out.append('""' + "\n" * src.count("\n", m.start(), j))
            i = j
        else:  # character literal
            out.append(tok)
            i = m.end()
    return "".join(out)


# ---------------------------------------------------------------------------------------------
# Counting

_SET_OPTION = re.compile(r"\bset_option\s+([A-Za-z_][\w.]*)\s+([^\s\]]+)(\s+in\b)?")
_NOLINT = re.compile(r"\bnolint((?:\s+[A-Za-z_][\w.]*)+)")
_SIMPLE = {
    "sorry": re.compile(r"(?<![\w.'])sorry(?![\w'])"),
    "admit": re.compile(r"(?<![\w.'])admit(?![\w'])"),
    "axiom declarations": re.compile(
        r"^[ \t]*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|public|noncomputable|unsafe)\s+)*"
        r"axiom\s", re.M),
    "@[deprecated]": re.compile(r"@\[[^\]]*(?<![\w.])deprecated(?![\w.])"),
    "erw": re.compile(r"(?<![\w.'])erw(?![\w'])"),
    "#adaptation_note": re.compile(r"#adaptation_note\b"),
}


def count_source(src):
    """Counter of (category, item) -> number of occurrences in one file."""
    code = strip_comments(src)
    c = Counter()
    for name, rx in _SIMPLE.items():
        k = len(rx.findall(code))
        if k:
            c[(OTHER, name)] += k
    for m in _SET_OPTION.finditer(code):
        opt, val, scoped = m.group(1), m.group(2), bool(m.group(3))
        if opt.startswith("linter.") and val == "false":
            c[(LINTER, f"set_option {opt} false")] += 1
            c[(LINTER_SCOPE, "set_option ... in" if scoped else "file/section-wide set_option")] += 1
        elif opt in LIMIT_DEFAULTS:
            default = LIMIT_DEFAULTS[opt]
            try:
                v = int(val.replace("_", ""))
            except ValueError:
                kind = "set to a non-literal value"
            else:
                if v == 0 and opt != "synthInstance.maxSize":
                    kind = "0 (unlimited)"
                elif v > default:
                    kind = "raised"
                elif v < default:
                    kind = f"lowered (below the default {default})"
                else:
                    kind = "reset to the default"
            c[(LIMITS, f"{opt} {kind}")] += 1
        elif opt.startswith("backward."):
            c[(BACKWARD, f"set_option {opt}")] += 1
    for m in _NOLINT.finditer(code):
        for name in m.group(1).split():
            c[(LINTER, f"@[nolint {name}]")] += 1
            c[(LINTER_SCOPE, "@[nolint] attribute")] += 1
    return c


def in_scope(path):
    # The comparator challenges are statements whose proofs are `sorry` by design.
    return (path.endswith(".lean") and path.startswith(ROOTS)
            and not (path.startswith("Comparator/") and path.endswith("/Challenge.lean")))


def git(*args, **kw):
    return subprocess.run(["git", *args], check=True, stdout=subprocess.PIPE, **kw).stdout


def read_blobs(rev, paths):
    """Contents of `rev:path` for each path (missing paths are skipped), via `git cat-file`."""
    if not paths:
        return {}
    data = git("cat-file", "--batch", input="".join(f"{rev}:{p}\n" for p in paths).encode())
    result, pos = {}, 0
    for p in paths:
        nl = data.index(b"\n", pos)
        header = data[pos:nl].split()
        pos = nl + 1
        if header[-1:] == [b"missing"]:
            continue
        size = int(header[2])
        result[p] = data[pos:pos + size].decode("utf-8", "replace")
        pos += size + 1
    return result


def count_files(contents):
    """{path: Counter} for files with any debt."""
    per_file = {}
    for path, src in contents.items():
        c = count_source(src)
        if c:
            per_file[path] = c
    return per_file


def count_rev(rev):
    """{path: Counter} at commit `rev`, or in the working tree if `rev` is None."""
    if rev is None:
        paths = [p for p in git("ls-files", "-z").decode().split("\0") if in_scope(p)]
        contents = {}
        for p in paths:
            with open(p, encoding="utf-8", errors="replace") as f:
                contents[p] = f.read()
        return count_files(contents)
    paths = [p for p in git("ls-tree", "-r", "-z", "--name-only", rev).decode().split("\0")
             if in_scope(p)]
    return count_files(read_blobs(rev, paths))


def totals(per_file):
    t = Counter()
    for c in per_file.values():
        t.update(c)
    return t


# ---------------------------------------------------------------------------------------------
# Serialisation

def to_json(rev, per_file):
    return {
        "rev": rev,
        "totals": [[cat, item, n] for (cat, item), n in sorted(totals(per_file).items())],
        "files": {f: [[cat, item, n] for (cat, item), n in sorted(c.items())]
                  for f, c in sorted(per_file.items())},
    }


def from_json(obj):
    return {f: Counter({(cat, item): n for cat, item, n in rows})
            for f, rows in obj["files"].items()}


def category_totals(t):
    """Per category: (category, total). The scope breakdown is not a separate total."""
    ct = Counter()
    for (cat, _), n in t.items():
        if cat != LINTER_SCOPE:
            ct[cat] += n
    return ct


def ordered_keys(keys):
    return sorted(keys, key=lambda k: (CATEGORIES.index(k[0]) if k[0] in CATEGORIES else 99, k[1]))


def sign(n):
    return f"+{n}" if n > 0 else str(n)


def md_escape(s):
    return s.replace("|", "\\|")


# ---------------------------------------------------------------------------------------------
# Commands

def cmd_count(args):
    per_file = count_rev(args.rev)
    t = totals(per_file)
    if args.format == "json":
        rev = git("rev-parse", args.rev).decode().strip() if args.rev else "worktree"
        json.dump(to_json(rev, per_file), sys.stdout, indent=1, sort_keys=True)
        print()
        return
    if args.per_file:
        rows = sorted((f, cat, item, n) for f, c in per_file.items() for (cat, item), n in c.items())
        for row in rows:
            print("\t".join(map(str, row)))
        return
    if args.format == "tsv":
        for cat, item in ordered_keys(t):
            print(f"{cat}\t{item}\t{t[(cat, item)]}")
        return
    ct = category_totals(t)
    for cat in CATEGORIES:
        keys = [k for k in ordered_keys(t) if k[0] == cat]
        if not keys:
            continue
        total = f"{ct[cat]:>8}" if cat != LINTER_SCOPE else " " * 8
        print(f"{total}  {cat}")
        for k in keys:
            print(f"{t[k]:>8}    {k[1]}")


def load_side(spec):
    if os.path.isfile(spec):
        with open(spec) as f:
            obj = json.load(f)
        return obj["rev"], from_json(obj)
    return git("rev-parse", spec).decode().strip(), None


def cmd_diff(args):
    base_rev, base = load_side(args.base)
    head_rev, head = load_side(args.head)
    if head is None:
        head = count_rev(head_rev)
    if base is None:
        # BASE = HEAD with the files that differ replaced by their BASE versions.
        changed = [p for p in git("diff", "-z", "--name-only", "--no-renames", base_rev, head_rev)
                   .decode().split("\0") if in_scope(p)]
        old = count_files(read_blobs(base_rev, changed))
        base = {f: c for f, c in head.items() if f not in changed}
        base.update(old)
    tb, th = totals(base), totals(head)
    keys = ordered_keys(set(tb) | set(th))
    changed_keys = [k for k in keys if tb[k] != th[k]]
    file_deltas = []
    for f in sorted(set(base) | set(head)):
        b, h = base.get(f, Counter()), head.get(f, Counter())
        d = {k: h[k] - b[k] for k in set(b) | set(h) if h[k] != b[k] and k[0] != LINTER_SCOPE}
        if d:
            file_deltas.append((f, d))
    if args.format == "tsv":
        for k in keys:
            print(f"{k[0]}\t{k[1]}\t{tb[k]}\t{th[k]}\t{th[k] - tb[k]}")
        return
    if args.format == "table":
        for k in changed_keys:
            print(f"{th[k]:>8} {sign(th[k] - tb[k]):>7}  {k[0]}: {k[1]}")
        if not changed_keys:
            print("no changes")
        return
    # markdown
    url = args.repo_url
    link = (lambda r: f"[`{r[:10]}`]({url}/commit/{r})") if url else (lambda r: f"`{r[:10]}`")
    def fold(title, body):
        # GitHub renders HTML <details>; Zulip has spoiler blocks instead.
        if args.flavor == "zulip":
            return [f"```spoiler {title}", *body, "```"]
        return [f"<details><summary>{title}</summary>", "", *body, "", "</details>"]

    cb, ch = category_totals(tb), category_totals(th)
    lines = []
    if not changed_keys and not args.full:
        lines.append("No changes to the technical-debt counters.")
    else:
        lines.append("| Category | Before | After | Change |")
        lines.append("|:-|-:|-:|-:|")
        for cat in CATEGORIES:
            if cat == LINTER_SCOPE or (cb[cat] == ch[cat] == 0):
                continue
            mark = f"**{sign(ch[cat] - cb[cat])}**" if ch[cat] != cb[cat] else "0"
            lines.append(f"| {cat} | {cb[cat]} | {ch[cat]} | {mark} |")
    if changed_keys:
        lines.append("")
        lines += fold("Changed counters", ["| Counter | Before | After | Change |", "|:-|-:|-:|-:|"] + [
            f"| {k[0]}: `{md_escape(k[1])}` | {tb[k]} | {th[k]} | {sign(th[k] - tb[k])} |"
            for k in changed_keys])
    if args.full:
        lines.append("")
        lines += fold("All counters", ["| Counter | Now | Change |", "|:-|-:|-:|"] + [
            f"| {k[0]}: `{md_escape(k[1])}` | {th[k]} | {sign(th[k] - tb[k]) if th[k] != tb[k] else ''} |"
            for k in keys if th[k]])
    if file_deltas and args.max_files:
        lines.append("")
        shown = sorted(file_deltas, key=lambda fd: (-sum(abs(v) for v in fd[1].values()), fd[0]))
        body = ["| File | Changes |", "|:-|:-|"]
        for f, d in shown[:args.max_files]:
            desc = ", ".join(f"{sign(v)} `{md_escape(k[1])}`" for k, v in
                             sorted(d.items(), key=lambda kv: (CATEGORIES.index(kv[0][0]), kv[0][1])))
            body.append(f"| `{md_escape(f)}` | {desc} |")
        if len(shown) > args.max_files:
            body.append(f"| ... | {len(shown) - args.max_files} more files |")
        lines += fold(f"Changes per file ({len(file_deltas)} files)", body)
    lines.append("")
    lines.append(f"Base {link(base_rev)}, head {link(head_rev)}. Counted by `scripts/tech_debt/metrics.py` "
                 "(comments and strings excluded).")
    print("\n".join(lines))


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("count", help="count the technical debt of one tree")
    c.add_argument("--rev", help="commit to read (default: the working tree)")
    c.add_argument("--format", choices=["table", "tsv", "json"], default="table")
    c.add_argument("--per-file", action="store_true", help="one TSV row per file and counter")
    d = sub.add_parser("diff", help="compare two trees")
    d.add_argument("base")
    d.add_argument("head")
    d.add_argument("--format", choices=["markdown", "table", "tsv"], default="markdown")
    d.add_argument("--max-files", type=int, default=40, help="files listed in the markdown (0: none)")
    d.add_argument("--repo-url", help="https://github.com/OWNER/REPO, for commit links")
    d.add_argument("--flavor", choices=["github", "zulip"], default="github", help="markdown dialect")
    d.add_argument("--full", action="store_true", help="always show the category table, and all counters")
    args = p.parse_args()
    (cmd_count if args.cmd == "count" else cmd_diff)(args)


if __name__ == "__main__":
    main()
