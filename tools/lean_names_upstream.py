#!/usr/bin/env python3
"""Additional Lean names for the nodes, read from the current source repositories (decision of the human, 2026-10-10).

Usage:
  tools/lean_names_upstream.py blueprint [--repo DIR] [--ref REF]
      the `lean = [...]` lists of the blueprint nodes of the blueprint repository at REF
      (default: ~/weil-conjectures-slopmaster2, branch upstream-blueprint-main); only the lists are read, no blueprint text
  tools/lean_names_upstream.py docstrings <sorry map> [--repo DIR] [--ref REF]
      the declarations whose docstring carries `(blueprint: <node id>)` in the Lean source at REF (default HEAD of the
      done-branch checkout), located with the module and line ranges of the sorry map made from that same commit
  tools/lean_names_upstream.py show
      counts

Both write their part into dag/lean_names_upstream.json:
  {"blueprint": {"ref", "commit", "names": {node id: [names]}},
   "docstring": {"ref", "commit", "names": {node id: [names]}, "tags": n, "matched_declarations": n, "unknown_ids": [...]}}
`tools/lean_status.py --extra <branch>=dag/lean_names_upstream.json` adds these names to the nodes' declarations on that
branch. Node ids that are not DAG nodes are ignored (listed under unknown_ids for the docstrings).
"""
from __future__ import annotations
import collections, gzip, json, pathlib, re, subprocess, sys, tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "dag" / "lean_names_upstream.json"
REPO = pathlib.Path.home() / "weil-conjectures-slopmaster2"
TAG = re.compile(r"\(blueprint:\s*([A-Za-z0-9][A-Za-z0-9:_.-]*)\s*\)")


def git(repo, *a) -> str:
    return subprocess.run(["git", *a], cwd=repo, capture_output=True, text=True, check=True).stdout


def node_ids() -> set[str]:
    return {p.stem for p in (ROOT / "dag" / "nodes").rglob("*.json")}


def load_out() -> dict:
    return json.loads(OUT.read_text()) if OUT.exists() else {}


def opt(args, name, default):
    if name in args:
        i = args.index(name); v = args[i + 1]; del args[i:i + 2]; return v
    return default


def cmd_blueprint(args) -> int:
    repo = pathlib.Path(opt(args, "--repo", str(REPO))); ref = opt(args, "--ref", "upstream-blueprint-main")
    ids = node_ids()
    names, total = {}, 0
    for path in git(repo, "ls-tree", "-r", "--name-only", ref).splitlines():
        if not (path.startswith("blueprint/") and path.endswith(".md")):
            continue
        text = git(repo, "show", f"{ref}:{path}")
        m = re.match(r"\+\+\+\n(.*?)\n\+\+\+", text, re.S)
        if not m:
            continue
        try:
            fm = tomllib.loads(m.group(1))
        except tomllib.TOMLDecodeError:
            continue
        lean = fm.get("lean")
        if not lean:
            continue
        total += 1
        i = str(fm.get("id") or pathlib.PurePosixPath(path).stem)
        if i in ids:
            names[i] = [str(x) for x in lean]
    out = load_out()
    out["blueprint"] = {"ref": ref, "commit": git(repo, "rev-parse", "--short", ref).strip(), "names": dict(sorted(names.items())),
                        "lists_in_repo": total}
    OUT.write_text(json.dumps(out, ensure_ascii=False, indent=1) + "\n")
    print(f"blueprint lean lists: {total} in {ref}, {len(names)} for DAG nodes, {sum(len(v) for v in names.values())} names")
    return 0


def cmd_docstrings(args) -> int:
    repo = pathlib.Path(opt(args, "--repo", str(REPO))); ref = opt(args, "--ref", "HEAD")
    if not args:
        print(__doc__); return 2
    smap = args[0]
    opener = gzip.open if smap.endswith(".gz") else open
    by_module = collections.defaultdict(list)          # module -> [(l1, l2, owner)]
    with opener(smap, "rt") as fh:
        for line in fh:
            r = json.loads(line)
            if r["n"] == r["o"] and r.get("m"):
                by_module[r["m"]].append((r["l1"], r["l2"], r["o"]))
    for v in by_module.values():
        v.sort()
    ids = node_ids()
    names, unknown, tags, matched = collections.defaultdict(list), set(), 0, set()
    out_grep = subprocess.run(["git", "grep", "-n", "-E", r"\(blueprint: *[A-Za-z0-9]", ref, "--", "*.lean"], cwd=repo,
                              capture_output=True, text=True).stdout
    for line in out_grep.splitlines():
        _, path, lno, text = line.split(":", 3) if line.count(":") >= 3 else (None, None, None, None)
        if path is None:
            continue
        module = path[:-5].replace("/", ".")
        decls = by_module.get(module, [])
        lno = int(lno)
        for nid in TAG.findall(text):
            tags += 1
            nid = nid.replace(":", "-", 1) if nid not in ids and nid.replace(":", "-", 1) in ids else nid
            if nid not in ids:
                unknown.add(nid); continue
            # the declaration the docstring belongs to: the one whose range contains the line, else the next one after it
            owner = next((o for l1, l2, o in decls if l1 <= lno <= l2), None) or next((o for l1, l2, o in decls if l1 > lno), None)
            if owner:
                if owner not in names[nid]:
                    names[nid].append(owner)
                matched.add(owner)
    out = load_out()
    out["docstring"] = {"ref": ref, "commit": git(repo, "rev-parse", "--short", ref).strip(), "names": dict(sorted(names.items())),
                        "tags": tags, "matched_declarations": len(matched), "unknown_ids": sorted(unknown)}
    OUT.write_text(json.dumps(out, ensure_ascii=False, indent=1) + "\n")
    print(f"docstring tags: {tags}; declarations matched to a node: {len(matched)} for {len(names)} nodes; unknown ids: {len(unknown)}")
    return 0


def main() -> int:
    a = sys.argv[1:]
    if not a:
        print(__doc__); return 2
    if a[0] == "blueprint":
        return cmd_blueprint(a[1:])
    if a[0] == "docstrings":
        return cmd_docstrings(a[1:])
    if a[0] == "show":
        out = load_out()
        for k, v in out.items():
            print(k, v.get("commit"), len(v.get("names", {})), "nodes", sum(len(x) for x in v.get("names", {}).values()), "names",
                  {kk: vv for kk, vv in v.items() if kk in ("tags", "matched_declarations", "lists_in_repo")})
        return 0
    print(__doc__); return 2


if __name__ == "__main__":
    sys.exit(main())
