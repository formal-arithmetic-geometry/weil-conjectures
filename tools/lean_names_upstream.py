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
   "docstring": {"ref", "commit", "names": {node id: [names]}, "partial": {node id: [{name, text}]}, "tags": n,
                 "matched_declarations": n, "unknown_ids": [...]}}
A docstring tag with text beyond the ids ("(blueprint: `lem-x`, the implication (1) ⇒ (2))") says the declaration
states a part of the node: it goes under `partial`, and lean_status gives such a node at best `closed_part`.
`tools/lean_status.py --extra <branch>=dag/lean_names_upstream.json` adds these names to the nodes' declarations on that
branch. Node ids that are not DAG nodes are ignored (listed under unknown_ids for the docstrings).
"""
from __future__ import annotations
import collections, gzip, json, pathlib, re, subprocess, sys, tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "dag" / "lean_names_upstream.json"
REPO = pathlib.Path.home() / "weil-conjectures-slopmaster2"
SEG = re.compile(r"\(blueprint:([^)]*)")           # the text after "(blueprint:" up to ")" (or the end of the line)
ID = re.compile(r"`?([a-z][a-z0-9]*(?:[-:][a-z0-9.]+)+)`?")


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
    partial = collections.defaultdict(list)
    out_grep = subprocess.run(["git", "grep", "-n", "-E", r"\(blueprint:", ref, "--", "*.lean"], cwd=repo,
                              capture_output=True, text=True).stdout
    files: dict[str, list[str]] = {}
    unattached = 0
    for line in out_grep.splitlines():
        parts = line.split(":", 3)
        if len(parts) < 4:
            continue
        _, path, lno, text = parts
        lno = int(lno)
        if path not in files:
            files[path] = git(repo, "show", f"{ref}:{path}").splitlines()
        src = files[path]
        # the tag belongs to a declaration only if it sits in a `/--` docstring (not a `/-!` module or section docstring)
        k, opener = lno - 1, None
        while k >= 0:
            t = src[k]
            j1, j2 = t.rfind("/--"), t.rfind("/-!")
            if j1 >= 0 or j2 >= 0:
                opener = "doc" if j1 > j2 else "mod"; break
            if "-/" in t and k != lno - 1:
                break
            k -= 1
        module = path[:-5].replace("/", ".")
        decls = by_module.get(module, [])
        owner = None
        if opener == "doc":
            owner = next((o for l1, l2, o in decls if l1 <= lno <= l2), None) or next((o for l1, l2, o in decls if l1 > lno), None)
        for seg in SEG.findall(text):
            # text beyond the ids ("the implication (1) ⇒ (2)", "the fibrewise step of ...") qualifies the tag: the
            # declaration states only a part of the node (`partial`), not the node
            rest = re.sub(r"[`;,\s]", "", ID.sub("", seg))
            for nid in ID.findall(seg):
                tags += 1
                nid2 = nid.replace(":", "-", 1)
                nid = nid if nid in ids else (nid2 if nid2 in ids else nid)
                if nid not in ids:
                    unknown.add(nid); continue
                if not owner:
                    unattached += 1; continue
                if rest:
                    if owner not in [p["name"] for p in partial[nid]]:
                        partial[nid].append({"name": owner, "text": seg.strip()})
                    matched.add(owner); continue
                if owner not in names[nid]:
                    names[nid].append(owner)
                matched.add(owner)
    out = load_out()
    out["docstring"] = {"ref": ref, "commit": git(repo, "rev-parse", "--short", ref).strip(), "names": dict(sorted(names.items())),
                        "partial": dict(sorted(partial.items())),
                        "tags": tags, "matched_declarations": len(matched), "tags_not_in_a_declaration_docstring": unattached, "unknown_ids": sorted(unknown)}
    OUT.write_text(json.dumps(out, ensure_ascii=False, indent=1) + "\n")
    print(f"docstring tags (ids): {tags}; declarations matched to a node: {len(matched)}: exact for {len(names)} nodes, qualified (partial) for {len(partial)} nodes; ids that are no node: {len(unknown)}; node tags outside a declaration docstring: {unattached}")
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
