#!/usr/bin/env python3
"""Write the DAG as one snapshot file for the graph viewer in site/.

Usage:
  tools/export_snapshot.py <base snapshot> <output>

The base snapshot is the blueprint's own snapshot file (blueprint.json of the blueprint site). Four things are
taken from it, because the DAG does not hold them: the section objects, the `refines` edges that place a node
in its section, the KaTeX macros, and the facts about Lean declarations. Everything else comes from dag/nodes.

What the viewer shows for a node:
  kind      definition / statement / target
  edges     `stmt_dep` (needed to state the node) and `proof_dep` (used by a step of its proof); a dependency
            that is both is drawn as `stmt_dep`
  status    the viewer has five status keys; they are used for the stages of a node:
              proved_with_axioms  Mathlib leaf
              proved              Lean declaration found, its text has no sorry
              stated              Lean declaration found, its text has a sorry
              absent              split in words, no Lean
              missing             still to split (the stage-1 items of tools/dag_queue.py)
            a node no target reaches has no status
  body      the statement, the proof in steps, and the record (source, origin of the proof, Mathlib searches, flags)
  checks    one entry per import flag of a node
"""
from __future__ import annotations
import collections, json, pathlib, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEVEL = {"in_cycle": "error", "undischarged_input": "warning", "partial_undischarged_input": "warning",
         "citation_only": "warning", "open_problem": "warning"}


def body_of(d: dict, queued: bool) -> str:
    out = [d["statement"].strip()]
    if d["kind"] != "definition" or d["proof"]:
        out.append("## Proof")
        if d["proof"]:
            for i, s in enumerate(d["proof"], 1):
                note = "" if s.get("uses") else " *(cites no node; not judged elementary)*" if s.get("elementary") is None else ""
                out.append(f"**Step {i}.**{note} {s['text'].strip()}")
        else:
            out.append("*No proof in steps: the node is still to split.*" if queued else "*No proof recorded.*")
    if d.get("blueprint_proof_text"):
        out += ["## Blueprint text (a reference, not a proof)", d["blueprint_proof_text"].strip()]
    rec = []
    src = d.get("source") or {}
    rec.append(f"- source: `{src.get('document', '')}`, {src.get('place', '')}")
    for e in src.get("external") or []:
        rec.append(f"- cites: {e.get('document', '')}, {str(e.get('place', ''))[:120]}")
    po = d.get("proof_origin")
    if po:
        rec.append(f"- proof written by: {po.get('by', '')}")
    if d.get("mathlib_match"):
        rec.append("- Mathlib match: " + ", ".join(f"`{x}`" for x in d["mathlib_match"]))
    for s in d.get("mathlib_searches") or []:
        rec.append(f"- Mathlib search ({s.get('date', '')}, {s.get('tool', '')}): `{s.get('query', '')}` gave "
                   + (", ".join(map(str, s.get("results") or [])) or "nothing"))
    if not d.get("mathlib_searches"):
        rec.append("- Mathlib search: none made")
    ln = d.get("lean")
    if ln:
        rec.append(f"- Lean: `{ln.get('declaration')}` in `{ln.get('module')}` (branch {ln.get('branch')}, "
                   f"{'no sorry in its text' if ln.get('sorry_free') else 'sorry in its text'}, body {ln.get('body_lines')} lines)")
    if d.get("import_flags"):
        rec.append("- import flags: " + ", ".join(d["import_flags"]))
    out += ["## Record", "\n".join(rec)]
    return "\n\n".join(out)


def main() -> None:
    base = json.loads(pathlib.Path(sys.argv[1]).read_text())
    nodes = {}
    for p in sorted((ROOT / "dag/nodes").rglob("*.json")):
        d = json.loads(p.read_text())
        nodes[d["id"]] = d
    items = subprocess.run([sys.executable, str(ROOT / "tools/dag_queue.py"), "items"], capture_output=True, text=True, check=True).stdout
    queued = {l.split("\t")[1] for l in items.splitlines() if l.split("\t")[0] == "1"}
    stage2 = {l.split("\t")[1] for l in items.splitlines() if l.split("\t")[0] == "2"}

    kinds = base["schema"]["kinds"]
    edge = dict(kinds["uses"])
    schema = {
        "definition": kinds["definition"],
        "statement": dict(kinds["lemma"]),
        "target": dict(kinds["theorem"], color="#b03060"),
        "section": kinds["section"],
        "refines": kinds["refines"],
        "stmt_dep": dict(edge, color="#c2571a"),
        "proof_dep": dict(edge, color="#667"),
    }

    objects, status, checks = [], {}, []
    sections = {o["id"]: o for o in base["objects"] if o["kind"] == "section"}
    objects += sections.values()
    ids = set(nodes) | set(sections)
    for o in base["objects"]:
        if o["kind"] == "refines" and all(b["id"] in ids for b in o["boundary"]):
            objects.append(o)

    for i, d in nodes.items():
        unreachable = "unreachable" in d["import_flags"]
        kind = "target" if d.get("target") else d["kind"]
        ln = d.get("lean")
        tags = list(d["import_flags"]) + (["stage2_open"] if i in stage2 else [])
        attrs = {"title": d["title"], "order": d["blueprint_order"], "tags": tags}
        if ln:
            attrs["lean"] = [x for x in d.get("blueprint_lean", [ln["declaration"]] if ln.get("declaration") else []) if x not in d.get("blueprint_lean_not_found", [])]
        objects.append({"source": {"file": d["source"]["document"], "anonymous": False}, "kind": kind, "id": i,
                        "depth": 0, "boundary": [], "body": body_of(d, i in queued), "attrs": attrs})
        if not unreachable:
            status[i] = ("proved_with_axioms" if d["status"] == "mathlib" else "missing" if i in queued
                         else ("proved" if ln.get("sorry_free") else "stated") if ln else "absent")
        stmt = [t for t in dict.fromkeys(d["stmt_deps"]) if t in nodes and t != i]
        proof = [t for t in dict.fromkeys(d["proof_deps"]) if t in nodes and t != i and t not in stmt]
        for k, ts in (("stmt_dep", stmt), ("proof_dep", proof)):
            for t in ts:
                objects.append({"source": {"file": d["source"]["document"], "anonymous": True}, "kind": k,
                                "id": f"{k}/{i}/{t}", "depth": 1,
                                "boundary": [{"role": "src", "id": i}, {"role": "tgt", "id": t}], "body": "", "attrs": {}})
        for f in d["import_flags"]:
            checks.append({"objects": [i], "message": f"{i}: {f.replace('_', ' ')}", "level": LEVEL.get(f, "info"), "code": f})

    # progress of a section: its nodes that are Mathlib leaves or have Lean without sorry, over all its nodes
    parent = collections.defaultdict(list)
    for o in objects:
        if o["kind"] == "refines":
            b = {x["role"]: x["id"] for x in o["boundary"]}
            parent[b["src"]].append(b["tgt"])
    prog = collections.defaultdict(lambda: {"total": 0, "proved": 0})
    for i in nodes:
        if i not in status:
            continue
        seen, todo = set(), list(parent[i])
        while todo:
            s = todo.pop()
            if s in seen:
                continue
            seen.add(s)
            todo += parent[s]
            prog[s]["total"] += 1
            prog[s]["proved"] += status[i] in ("proved", "proved_with_axioms")

    used = {n for o in objects for n in o["attrs"].get("lean", [])}
    snap = {
        "version": base["version"],
        "schema": {"kinds": schema, "defaultCollapse": "refines"},
        "project": dict(base["project"], title="The Weil conjectures: SHEAF DAG", name="weil-conjectures-sheaf"),
        "objects": objects,
        "facts": {k: v for k, v in (base.get("facts") or {}).items() if k in used},
        "derived": {"status": status, "progress": {"refines": dict(prog)}, "checks": checks},
    }
    pathlib.Path(sys.argv[2]).write_text(json.dumps(snap, ensure_ascii=False))
    c = collections.Counter(o["kind"] for o in objects)
    print(dict(c)); print(dict(collections.Counter(status.values())), "no status:", len(nodes) - len(status)); print("checks", len(checks))


if __name__ == "__main__":
    main()
