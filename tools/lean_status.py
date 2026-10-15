#!/usr/bin/env python3
"""Where each node stands in Lean, read from the compiled project and written into the nodes.

Usage:
  tools/lean_status.py <branch>=<sorry map>|<branch>=latest [<branch>=<sorry map> ...] [--extra <branch>=dag/lean_names_upstream.json]
                       [--library <branch>=local/library_names_mathlib.tsv.gz]

--library (2026-10-10): the declarations of the libraries the project imports (Mathlib, Lean core, ...; one line
`name<TAB>module<TAB>kind`, made by tools/library_names.lean in the checkout). A name of the node that is not in the
project but is in the library counts as found and sorry-free (`library: true` in decls, lines [0, 0]): a node whose
names are all library declarations is a Mathlib leaf and closed.

--extra (decision of the human, 2026-10-10): for that branch the node's declarations also include the names of
tools/lean_names_upstream.py: the current blueprint's `lean = [...]` list of the node and the declarations whose docstring
carries `(blueprint: <node id>)`. A declaration whose tag is qualified ("the implication (1) ⇒ (2)"; the `partial`
part of that file) is listed in decls with `partial: <tag text>` and never closes the node: a node with only such
declarations is at best `closed_part` (an attachment-check item for a worker). When the current blueprint has a list for the node, an old `blueprint_lean` name that is not
on the branch is recorded under `superseded` (renamed or dropped by the humans) instead of `missing`.

`<branch>=latest` (2026-10-11) takes the newest committed map local/sorry_map_<branch>_<base sha>.jsonl.gz (newest_map below:
the map whose last commit in git is the most recent, by file mtime when not committed; the old `_full` map is skipped);
tools/attach.py reads the same one.

A sorry map is the output of tools/sorry_map.lean for one branch (read plain or gzip-compressed, `.jsonl` or `.jsonl.gz`): every declaration of the project, whether its
own term contains `sorry`, and the project declarations it uses. Auxiliary declarations are merged into their owner.

The declarations of a node are the names in its `blueprint_lean`, plus the names the detailed LaTeX blueprint
gives for the same label, plus, for a node a worker created (`created` set) or the lead attached to (`lean.note` starting "attached by the lead"), the names already in its `lean_audit` decls; minus the names in `lean_names_rejected` (a declaration the blueprint named that states something else, with the reason) (`\\lean{...}` after `\\label{...}`; a label matches a node when it is the node id
with `:` for the first `-`). For each branch the node gets, in `lean_audit[branch]`:

  state   none            no declaration of the node exists on the branch
          closed          every declaration exists and no `sorry` is reachable from them
          sorry_here      a declaration of the node contains `sorry` itself
          rests_on_sorry  the node's declarations contain no `sorry`, but they use declarations that do
  open    for rests_on_sorry: the nearest declarations with `sorry` (reached through sorry-free ones), each with
          the node it belongs to, if any, and whether that node is below this one in the DAG. One with no node
          is a statement the Lean has split off and the DAG does not have.
  decls   the declarations found, with module, lines and kind; `missing` the names not found

It also writes dag/lean_audit.json (counts, and for each branch every declaration with `sorry` and its node)
"""
from __future__ import annotations
import collections, json, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
TEX = ROOT / "literature/blueprint/slopmaster2/src/version"


def newest_map(branch="slopmaster2"):
    """The newest sorry map of a branch in local/: by the time of its last commit in git (file mtime when not committed)."""
    import subprocess
    maps = [p for p in (ROOT / "local").glob(f"sorry_map_{branch}_*.jsonl.gz") if "_full" not in p.name]
    if not maps:
        return None

    def when(p):
        t = subprocess.run(["git", "log", "-1", "--format=%ct", "--", str(p.relative_to(ROOT))], cwd=ROOT,
                           capture_output=True, text=True).stdout.strip()
        return (int(t) if t else 1 << 62, p.stat().st_mtime)
    return max(maps, key=when)


def load_map(path):
    own = {}                                   # owner -> record
    deps = collections.defaultdict(set)
    import gzip
    opener = gzip.open if str(path).endswith(".gz") else open
    with opener(path, "rt") as fh:
        rows = [json.loads(l) for l in fh]
    owner = {r["n"]: r["o"] for r in rows}
    for r in rows:
        o = r["o"]
        rec = own.setdefault(o, {"sorry": False, "kind": None, "module": None, "l1": 0, "l2": 0})
        rec["sorry"] |= r["s"] or r["ts"]
        if r["n"] == o:
            rec.update(kind=r["k"], module=r["m"], l1=r["l1"], l2=r["l2"])
        for d in r["d"]:
            if owner.get(d, d) != o:
                deps[o].add(owner.get(d, d))
    return own, deps


def tex_names(node_ids):
    out = collections.defaultdict(list)
    for p in sorted(TEX.rglob("*.tex")):
        label = None
        for m in re.finditer(r"\\label\{([^}]*)\}|\\lean\{([^}]*)\}", p.read_text(errors="replace")):
            if m.group(1) is not None:
                label = m.group(1)
            elif label:
                i = label.replace(":", "-", 1)
                if i in node_ids:
                    out[i] += [x.strip() for x in m.group(2).split(",") if x.strip()]
    return out


def hand_names(d):
    """Declarations a worker attached by hand to a node it created (`created` set): the names in its lean_audit decls;
    and (2026-10-12) the declarations of a stage-2 record of an existing source declaration (`lean.branch`
    slopmaster2, `existing` not false): the record names them, whatever its note (the stage-2 records of 2026-10-11 04:46
    replaced the "attached by the lead" notes)."""
    rec = d.get("lean") or {}
    out = []
    if rec.get("branch") == "slopmaster2" and rec.get("existing") is not False:
        out += [x for x in [rec.get("declaration")] + list(rec.get("declarations") or []) if isinstance(x, str) and x]
    if not d.get("created") and not rec.get("note", "").startswith("attached by the lead"):
        return out
    for a in (d.get("lean_audit") or {}).values():
        if isinstance(a, dict):
            out += [x["name"] for x in a.get("decls") or [] if isinstance(x, dict) and x.get("name")]
    return out


def main():
    extra_by_branch, lib_by_branch, argv = {}, {}, []
    a = sys.argv[1:]
    while a:
        x = a.pop(0)
        if x == "--library" and a:
            b, f = a.pop(0).split("=", 1)
            import gzip
            with (gzip.open if f.endswith(".gz") else open)(f, "rt") as fh:
                lib_by_branch[b] = {r[0]: (r[1], r[2]) for r in (l.rstrip("\n").split("\t") for l in fh) if len(r) == 3}
        elif x == "--extra" and a:
            b, f = a.pop(0).split("=", 1)
            u = json.loads(pathlib.Path(f).read_text())
            bp = (u.get("blueprint") or {}).get("names", {})
            ds = (u.get("docstring") or {}).get("names", {})
            extra_by_branch[b] = {"blueprint": bp, "docstring": ds, "partial": (u.get("docstring") or {}).get("partial", {})}
        else:
            argv.append(x)
    paths = {p.read_text() and json.loads(p.read_text())["id"]: p for p in (ROOT / "dag/nodes").rglob("*.json")}
    nodes = {i: json.loads(p.read_text()) for i, p in paths.items()}
    extra = tex_names(set(nodes))
    names = {i: [n for n in dict.fromkeys(d.get("blueprint_lean", []) + extra.get(i, []) + hand_names(d))
                 if n not in {r["name"] for r in d.get("lean_names_rejected", [])}] for i, d in nodes.items()}
    node_of = collections.defaultdict(list)
    for i, ns in names.items():
        for n in ns:
            node_of[n].append(i)
    below = {}

    def desc(i):                                  # the nodes below i in the DAG
        if i not in below:
            seen, todo = set(), [i]
            while todo:
                x = todo.pop()
                for y in nodes[x]["stmt_deps"] + nodes[x]["proof_deps"]:
                    if y in nodes and y not in seen:
                        seen.add(y); todo.append(y)
            below[i] = seen
        return below[i]

    summary = {"names_from_blueprint": sum(len(d.get("blueprint_lean", [])) for d in nodes.values()),
               "nodes_with_names": sum(1 for v in names.values() if v), "branches": {}}
    for d in nodes.values():
        d["lean_audit"] = {}
    for arg in argv:
        branch, path = arg.split("=", 1)
        if path == "latest":
            path = newest_map(branch)
            print(branch, "sorry map", path.relative_to(ROOT))
        ex = extra_by_branch.get(branch)
        lib = lib_by_branch.get(branch, {})
        own, deps = load_map(path)
        reach_sorry = {}

        def frontier(start):
            """nearest owners with sorry reachable from the owners in start, not passing through one"""
            seen, todo, out = set(start), list(start), set()
            while todo:
                x = todo.pop()
                for y in deps.get(x, ()):
                    if y in seen or y not in own:
                        continue
                    seen.add(y)
                    if own[y]["sorry"]:
                        out.add(y)
                    else:
                        todo.append(y)
            return out

        counts = collections.Counter()
        for i, d in nodes.items():
            ns, superseded = list(names[i]), []
            if ex:
                up = ex["blueprint"].get(i)
                ns = list(dict.fromkeys(ns + (up or []) + ex["docstring"].get(i, [])))
                if up is not None:
                    superseded = [n for n in d.get("blueprint_lean", []) if n not in own and n not in up]
                    ns = [n for n in ns if n not in superseded]
                for n in ns:
                    if i not in node_of[n]:
                        node_of[n].append(i)
            found = [n for n in ns if n in own]
            in_lib = [n for n in ns if n not in own and n in lib]       # a library declaration (Mathlib, core): sorry-free
            missing = [n for n in ns if n not in own and n not in lib]
            # declarations whose docstring tag says they state a part of the node: listed, never closing the node
            partial = [p for p in (ex["partial"].get(i, []) if ex else []) if p["name"] in own and p["name"] not in ns]
            a = {"state": "none", "decls": [dict(name=n, module=own[n]["module"], lines=[own[n]["l1"], own[n]["l2"]],
                                                   kind=own[n]["kind"], sorry=own[n]["sorry"]) for n in found]
                 + [dict(name=n, module=lib[n][0], lines=[0, 0], kind=lib[n][1], sorry=False, library=True) for n in in_lib]
                 + [dict(name=p["name"], module=own[p["name"]]["module"], lines=[own[p["name"]]["l1"], own[p["name"]]["l2"]],
                         kind=own[p["name"]]["kind"], sorry=own[p["name"]]["sorry"], partial=p["text"]) for p in partial],
                 "missing": missing}
            if superseded:
                a["superseded"] = superseded
            if found or in_lib:
                if any(own[n]["sorry"] for n in found):
                    a["state"] = "sorry_here"
                fr = sorted(frontier([n for n in found if not own[n]["sorry"]]) - set(found))
                if fr and a["state"] == "none":
                    a["state"] = "rests_on_sorry"
                elif a["state"] == "none":
                    a["state"] = "closed" if not missing else "closed_part"
                a["open"] = [dict(name=f, module=own[f]["module"], lines=[own[f]["l1"], own[f]["l2"]], kind=own[f]["kind"],
                                  nodes=node_of.get(f, []), below=any(x in desc(i) for x in node_of.get(f, []))) for f in fr]
            elif partial:
                pf = [p["name"] for p in partial]
                if any(own[n]["sorry"] for n in pf):
                    a["state"] = "sorry_here"
                fr = sorted(frontier([n for n in pf if not own[n]["sorry"]]) - set(pf))
                a["state"] = "rests_on_sorry" if fr and a["state"] == "none" else ("closed_part" if a["state"] == "none" else a["state"])
                a["open"] = [dict(name=f, module=own[f]["module"], lines=[own[f]["l1"], own[f]["l2"]], kind=own[f]["kind"],
                                  nodes=node_of.get(f, []), below=any(x in desc(i) for x in node_of.get(f, []))) for f in fr]
            d["lean_audit"][branch] = a
            counts[a["state"]] += 1
        sorries = [dict(name=n, kind=r["kind"], module=r["module"], lines=[r["l1"], r["l2"]], nodes=node_of.get(n, []))
                   for n, r in sorted(own.items()) if r["sorry"]]
        summary["branches"][branch] = {
            "declarations": len(own), "with_sorry": len(sorries),
            "with_sorry_by_kind": dict(collections.Counter(s["kind"] for s in sorries)),
            "with_sorry_and_no_node": sum(1 for s in sorries if not s["nodes"]),
            "node_states": dict(counts), "sorries": sorries}
    for i, d in nodes.items():
        # re-read the file and change only lean_audit, so that a worker writing its item meanwhile loses nothing
        cur = json.loads(paths[i].read_text())
        if cur.get("lean_audit") == d["lean_audit"]:
            continue
        cur["lean_audit"] = d["lean_audit"]
        paths[i].write_text(json.dumps(cur, ensure_ascii=False, indent=1) + "\n")
    (ROOT / "dag/lean_audit.json").write_text(json.dumps(summary, ensure_ascii=False, indent=1) + "\n")
    for b, s in summary["branches"].items():
        print(b, {k: v for k, v in s.items() if k != "sorries"})
    print("nodes with names", summary["nodes_with_names"], "names from LaTeX labels", sum(len(v) for v in extra.values()), "for", len(extra), "nodes")


if __name__ == "__main__":
    main()
