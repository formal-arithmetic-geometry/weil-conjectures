#!/usr/bin/env python3
"""Mechanical part of the lead's review of a stage-1 delivery (stages/1-dag.md §2, coord/brief-stage1.md).

Usage:
  tools/review_split.py <item id> [<item id> ...]     check each item and the nodes created for it; exit 1 if anything fails

Checked, for the item: status is `split`; a statement has a proof in steps, each with text, `uses` and `elementary`
true/false, and `proof_deps` is exactly the union of the steps' `uses`; a definition has `stmt_deps`; every id cited exists
and is not merged; `proof_origin.by` is `document` or `agent` with a document; `split_report` is present; the blueprint_*
fields and import_flags of the committed version are unchanged (read from git HEAD).
The item's proof dependencies stay inside its unit's route, and the unit record is read (stages/1-dag.md §7).
For each node whose `created.item` is the item: id equals the file name, kind, statement, source and `created` are present,
at least one Mathlib search with a verdict, a `mathlib` status has a match, every id cited exists.
Blueprint references (stages/1-dag.md §6, rule of 2026-10-10): the item and every new node carry a well-formed `blueprint`
field with `from.place` filled (not "unspecified") and `same_as` a list (the whole blueprint was searched); a new node's
`from.node` is the item's nearest blueprint ancestor; the item's `split_report` has a `blueprint` entry naming the places of
the blueprint proof its steps realize.
It prints what it finds and changes nothing; the mathematical review is the lead's.
"""
from __future__ import annotations
import json, pathlib, subprocess, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import dag_queue as dq  # noqa: E402

ROOT = dq.li.ROOT


def head_version(path: pathlib.Path):
    try:
        out = subprocess.run(["git", "show", f"HEAD:{path.relative_to(ROOT)}"], cwd=ROOT, capture_output=True, text=True, check=True).stdout
        return json.loads(out)
    except (subprocess.CalledProcessError, json.JSONDecodeError):
        return None


def check_ids(d, nodes, merged, where, errs):
    for c in dq.deps_of(d, "all"):
        if c not in nodes:
            errs.append(f"{where}: cites {c}, no such node")
        elif c in merged:
            errs.append(f"{where}: cites {c}, merged into {merged[c]}")


def main() -> int:
    nodes = dq.load(); g = dq.Dag(nodes)
    files = {p.stem: p for p in dq.nodes_dir().rglob("*.json")}
    bad = 0
    for item in sys.argv[1:]:
        errs, notes = [], []
        d = nodes.get(item)
        if d is None:
            print(f"{item}: no such node"); bad += 1; continue
        leaf = str(d.get("status")) == "mathlib" and bool(d.get("mathlib_match"))
        if leaf:
            notes.append("the item is a Mathlib leaf")
        elif str(d.get("status")) != "split":
            errs.append(f"status is {d.get('status')!r}, not split")
        if not d.get("split_report"):
            errs.append("no split_report")
        po = d.get("proof_origin") or {}
        if dq.is_def(d):
            if not d.get("stmt_deps"):
                errs.append("definition with no stmt_deps")
        elif leaf:
            if d.get("proof"):
                errs.append("Mathlib leaf with proof steps")
        else:
            pf = d.get("proof")
            if not isinstance(pf, list) or not pf:
                errs.append("statement with no proof in steps")
            else:
                uses = []
                for k, s in enumerate(pf, 1):
                    if not isinstance(s, dict) or not s.get("text"):
                        errs.append(f"step {k}: no text"); continue
                    if s.get("elementary") not in (True, False):
                        errs.append(f"step {k}: elementary is {s.get('elementary')!r}")
                    if not s.get("uses") and s.get("elementary") is False:
                        errs.append(f"step {k}: not elementary and uses nothing")
                    uses += s.get("uses") or []
                if set(d.get("proof_deps") or []) != set(uses):
                    errs.append(f"proof_deps {sorted(set(d.get('proof_deps') or []) ^ set(uses))} differ from the union of uses")
            if po.get("by") not in ("document", "agent") or not po.get("document"):
                errs.append(f"proof_origin {po!r}")
            elif po.get("by") == "agent":
                notes.append("proof written by an agent")
        check_ids(d, nodes, g.merged, item, errs)
        # the unit route (stages/1-dag.md §7): proof dependencies on statements stay inside the unit's route
        import units as un
        units_, _ = un.load_units(); u = d.get("unit")
        if u and u in units_ and not dq.is_def(d) and (units_[u].get("uses") or units_[u].get("steps")):
            allowed = un.closure(units_, u)
            for c in dq.deps_of(d, "proof"):
                cn = nodes.get(c)
                if cn and not dq.is_def(cn) and not dq.is_leaf(cn) and not dq.finished(cn) and cn.get("unit") and cn.get("unit") not in allowed:
                    if c in (d.get("tool_uses") or []):
                        notes.append(f"tool use accepted: {c}"); continue
                    errs.append(f"route: proof uses {c} of unit {cn.get('unit')}, which {u} does not cite (a departure from the unit's route needs an established error, SETUP.md)")
        if u and u in units_:
            r = units_[u].get("realized") or {}
            if item in (r.get("statement") or []) or any(item in st for st in (r.get("steps") or [])):
                notes.append(f"realizes unit {u}")
            elif not (r.get("statement") or any(r.get("steps") or [])):
                notes.append(f"unit {u} has no realization recorded yet")
        hv = head_version(files[item])
        if hv:
            for k in list(hv):
                if k.startswith("blueprint_") or k in ("import_flags", "id", "kind", "lean_audit", "pointers"):
                    if k == "lean_audit" and str((d.get("lean") or {}).get("note", "")).startswith("attached by the lead"):
                        continue
                    if hv.get(k) != d.get(k):
                        errs.append(f"{k} changed from the committed version")
            if hv.get("statement") != d.get("statement"):
                notes.append("statement changed")
        new = [i for i, n in nodes.items() if (n.get("created") or {}).get("item") == item]
        for i in new:
            n = nodes[i]
            if files[i].stem != i:
                errs.append(f"new node {i}: file name differs")
            for k in ("kind", "statement", "source", "title"):
                if not n.get(k):
                    errs.append(f"new node {i}: no {k}")
            hv_new = head_version(files[i])
            if hv_new is not None and (hv_new.get("created") or {}).get("item") != item:
                errs.append(f"new node {i}: a committed node already had this id")
            ms = n.get("mathlib_searches") or []
            if not ms or not all(isinstance(m, dict) and m.get("query") and m.get("verdict") for m in ms):
                errs.append(f"new node {i}: no Mathlib search with a verdict")
            st = str(n.get("status"))
            if st == "mathlib" and not n.get("mathlib_match"):
                errs.append(f"new node {i}: status mathlib without a match")
            if st not in ("mathlib", "unsplit"):
                errs.append(f"new node {i}: status {st!r}")
            if st == "unsplit" and n.get("mathlib_match"):
                errs.append(f"new node {i}: has a match but is unsplit")
            check_ids(n, nodes, g.merged, f"new node {i}", errs)
        # blueprint references (stages/1-dag.md §6)
        import blueprint_refs as br
        bnodes, _ = br.load()
        strict = {item, *new}
        errs += [e for e in br.errors(bnodes, strict) if any(e.startswith(f"blueprint: {k} ") or e.startswith(f"blueprint: {k}:") for k in strict)]
        anc = br.ancestor_for_item(item, bnodes)
        for i in new:
            fr = ((bnodes.get(i) or {}).get("blueprint") or {}).get("from") or {}
            if isinstance(fr, dict) and fr.get("node") != anc:
                errs.append(f"blueprint: new node {i}: from.node is {fr.get('node')!r}, but the item's nearest blueprint ancestor is {anc!r}")
        sr = d.get("split_report")
        if isinstance(sr, dict) and not sr.get("blueprint"):
            errs.append("blueprint: split_report has no 'blueprint' entry naming the places of the blueprint proof the steps realize")
        print(f"{item}: {'PASS' if not errs else 'FAIL'}; {len(new)} new nodes" + (f" ({', '.join(new)})" if new else "") + ("; " + "; ".join(notes) if notes else ""))
        for e in errs:
            print("  " + e)
        bad += bool(errs)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
