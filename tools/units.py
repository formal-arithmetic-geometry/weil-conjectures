#!/usr/bin/env python3
"""The units and chapters of the blueprint, as records the tools can check (SETUP.md, the three levels; stages/1-dag.md §7).

Usage:
  tools/units.py build     write dag/chapters/<sec>.json (16) and dag/units/<sk>.json (389) from the blueprint, keeping the
                           `realized` fields already recorded, and stamp every node in dag/nodes/ with `chapter` and `unit`
  tools/units.py build --snapshot main-20261015 --unit <sk> [--unit <sk> ...]
                          build only the selected units and their chapters from that snapshot; stamp only their nodes.
                          Companion <sk>.proof.md files supply steps when _section.md has no inline proof.
                          Changed files have timestamped .bak copies (empty for a newly created file).
  tools/units.py route     print the unit route of the targets: the units reached from the targets' units through `uses`,
                           in breadth-first order, with their chapters
  tools/units.py check     the checks (also run by check_dag.py): every node has a chapter and a unit that exist; a unit whose
                           `realized` is filled has a node for its statement and for every step, and reaches every unit it cites;
                           a node whose direct dependencies leave its unit's route (a unit the unit does not cite, transitively)

Representation (stages/1-dag.md §7):
  dag/chapters/<sec>.json   id, title, key_theorem, reference, uses (chapters), text (verbatim), source
  dag/units/<sk>.json       id, chapter, title, lean, uses (units), statement (verbatim), steps [{text}] (the paragraphs of the
                            proof), source, and the binding fields
                              realized: {"statement": [node ids], "steps": [[node ids], ...]}   filled by the worker of the unit's key node
                              realized_by: {"date", "item"}                                   and confirmed on review
  a node                    chapter, unit (null for a chapter-level node), from its blueprint path; a node a worker created
                            inherits them from the item it was created for.
A node's route is its unit and the units its unit cites, transitively. The route is about proofs: a step of a statement in
unit U may use a statement of another unit only if U cites that unit (transitively); definitions, Mathlib leaves and finished nodes (closed Lean) are notions or tools, not route. A proof dependency outside the route is reported: an error for a split and reviewed node, a count for an imported one,
unless the lead accepted it as a tool use (`tool_uses` on the node, SETUP.md), which is counted separately.
A unit with no proof and no `uses` (a remark, an assembly) constrains nothing.
Reachability also honors a unit's explicit `realized` binding when all its statement and proof-step nodes
are reached, even if those nodes' source paths place them in another unit. Empty or partial bindings do not count.
"""
from __future__ import annotations
import argparse, collections, json, pathlib, re, sys, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import dag_queue as dq  # noqa: E402

ROOT = dq.li.ROOT
BP = ROOT / "literature/blueprint/master/blueprint"
UNITS = ROOT / "dag/units"
CHAPTERS = ROOT / "dag/chapters"
BACKUP_SUFFIX = f".units-{time.time_ns()}.bak"


def frontmatter(text: str) -> tuple[dict, str]:
    m = re.match(r"\+\+\+\n(.*?)\n\+\+\+\n?", text, re.S)
    fm = {}
    if m:
        for line in m.group(1).splitlines():
            if "=" in line:
                k, v = line.split("=", 1)
                k, v = k.strip(), v.strip()
                try:
                    fm[k] = json.loads(v)
                except json.JSONDecodeError:
                    fm[k] = v.strip('"')
        text = text[m.end():]
    return fm, text


def cut_steps(proof: str) -> list[dict]:
    paras = [p.strip() for p in re.split(r"\n\s*\n", proof.strip()) if p.strip()]
    paras = [p for p in paras if not re.match(r"^(Uses|Unresolved dependencies):", p)]
    # a displayed formula stays with its sentence
    out = []
    for p in paras:
        if out and (p.startswith("$$") or out[-1].endswith("$$") or out[-1].rstrip().endswith((",", ":"))):
            out[-1] += "\n\n" + p
        else:
            out.append(p)
    return [{"text": p} for p in out]


def dump(path: pathlib.Path, d: dict):
    text = json.dumps(d, ensure_ascii=False, indent=1) + "\n"
    previous = path.read_bytes() if path.exists() else b""
    if previous == text.encode():
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.with_name(path.name + BACKUP_SUFFIX).write_bytes(previous)
    path.write_text(text)


def source_place(doc, units, chapters):
    m = re.search(r"blueprint/[^/]+/blueprint/(sec-[^/]+)/(?:(sk-[^/]+)/)?[^/]+\.md$", doc)
    if m and m.group(1) in chapters:
        return m.group(1), (m.group(2) if m.group(2) in units else None)
    return None


def stamp_missing(d, units, chapters):
    """Complete absent live-import bindings from source metadata; keep explicit live bindings."""
    place = source_place(str((d.get("source") or {}).get("document") or ""), units, chapters)
    if place:
        for key, value in zip(("chapter", "unit"), place):
            if not d.get(key) and value is not None:
                d[key] = value
    return d


def node_place(i, nodes, files, units, chapters, seen=()):
    d = nodes[i]
    place = source_place(str((d.get("source") or {}).get("document") or ""), units, chapters)
    if place:
        return place
    item = (d.get("created") or {}).get("item")
    if item in nodes and item not in seen:
        return node_place(item, nodes, files, units, chapters, seen + (i,))
    return files[i].parent.name if files[i].parent.name in chapters else None, None


def build(bp=None, selected=None) -> None:
    bp = BP if bp is None else bp
    if not bp.is_dir():
        raise ValueError(f"blueprint snapshot is not available: {bp}")
    sections = sorted(bp.glob("sec-*"))
    if selected:
        found = {sk.name for sec in sections for sk in sec.glob("sk-*") if (sk / "_section.md").is_file()}
        if set(selected) - found:
            raise ValueError(f"units absent from {bp}: {', '.join(sorted(set(selected) - found))}")
    old_units = {p.stem: json.loads(p.read_text()) for p in UNITS.glob("*.json")} if UNITS.is_dir() else {}
    nch = nun = 0
    for sec in sections:
        sketches = [sk for sk in sorted(sec.glob("sk-*"))
                    if (sk / "_section.md").is_file() and (not selected or sk.name in selected)]
        if selected and not sketches:
            continue
        fm, body = frontmatter((sec / "_section.md").read_text())
        key = re.search(r"key theorem:\s*(.*)", body)
        ref = re.search(r"reference:\s*(.*)", body)
        dump(CHAPTERS / f"{sec.name}.json", {
            "id": sec.name, "kind": "chapter", "title": fm.get("title"), "uses": fm.get("uses", []),
            "key_theorem": key.group(1).strip() if key else None, "reference": ref.group(1).strip() if ref else None,
            "text": body.strip(), "source": str((sec / "_section.md").relative_to(ROOT))})
        nch += 1
        for sk in sketches:
            f = sk / "_section.md"
            if not f.is_file():
                continue
            fm, body = frontmatter(f.read_text())
            stmt, _, proof = body.partition("\n## Proof")
            companion = sk / f"{sk.name}.proof.md"
            if not proof.strip() and companion.is_file():
                _, proof = frontmatter(companion.read_text())
            rec = {"id": sk.name, "kind": "unit", "chapter": sec.name, "title": fm.get("title"), "lean": fm.get("lean", []),
                   "uses": fm.get("uses", []), "statement": stmt.strip(), "steps": cut_steps(proof) if proof.strip() else [],
                   "source": str(f.relative_to(ROOT))}
            old = old_units.get(sk.name, {})
            rec["realized"] = old.get("realized") or {"statement": [], "steps": [[] for _ in rec["steps"]]}
            rec["realized_by"] = old.get("realized_by")
            if len(rec["realized"]["steps"]) != len(rec["steps"]):
                rec["realized"]["steps"] = (rec["realized"]["steps"] + [[] for _ in rec["steps"]])[:len(rec["steps"])]
            dump(UNITS / f"{sk.name}.json", rec); nun += 1
    # stamp the nodes
    # build writes this repository. SHEAF_DAG is a read overlay and can point at
    # the live project when this command runs in an isolated side project.
    files = {p.stem: p for p in (ROOT / "dag/nodes").rglob("*.json")}
    nodes = {i: json.loads(p.read_text()) for i, p in files.items()}
    units = {p.stem for p in UNITS.glob("*.json")}; chapters = {p.stem for p in CHAPTERS.glob("*.json")}

    n = 0
    for i, d in nodes.items():
        ch, un = node_place(i, nodes, files, units, chapters)
        if selected and un not in selected:
            continue
        if d.get("chapter") != ch or d.get("unit") != un:
            d["chapter"], d["unit"] = ch, un
            dump(files[i], d); n += 1
    print(f"{nch} chapters, {nun} units written; {n} nodes stamped")


def load_units() -> tuple[dict, dict]:
    units = {p.stem: json.loads(p.read_text()) for p in UNITS.glob("*.json")} if UNITS.is_dir() else {}
    chapters = {p.stem: json.loads(p.read_text()) for p in CHAPTERS.glob("*.json")} if CHAPTERS.is_dir() else {}
    return units, chapters


def closure(units: dict, u: str) -> set[str]:
    out, st = set(), [u]
    while st:
        x = st.pop()
        if x in out:
            continue
        out.add(x); st += [v for v in units.get(x, {}).get("uses", []) if v in units]
    return out


def route(nodes=None, units=None, chapters=None):
    """units reached from the targets' units, breadth first: [(rank, unit, chapter)]"""
    nodes = nodes or dq.load(); units, chapters = (units, chapters) if units else load_units()
    g = dq.Dag(nodes)
    roots = [nodes[t].get("unit") for t in g.targets if nodes[t].get("unit")]
    rank, dqu = {}, collections.deque((r, 0) for r in roots)
    while dqu:
        u, k = dqu.popleft()
        if u in rank or u not in units:
            continue
        rank[u] = k
        for v in units[u].get("uses", []):
            if v not in rank:
                dqu.append((v, k + 1))
    return sorted(((k, u, units[u]["chapter"]) for u, k in rank.items()), key=lambda x: (x[0], x[1]))


def unit_bits(nodes, g, units, deps_all):
    """pfinc 2026-10-17 (cpu): for every node, the units (as bits of an int) of the nodes it reaches through g.deps(x, "all"),
    itself included; one pass over the strongly connected components (emitted children first). Only units of `units`."""
    import check_dag
    ubit = {u: 1 << k for k, u in enumerate(units)}
    graph = {x: deps_all(x) for x in nodes}
    comp_of, cbits = {}, []
    for comp in check_dag.sccs(graph):
        k = len(cbits)
        for m in comp:
            comp_of[m] = k
        bits = 0
        for m in comp:
            bits |= ubit.get(nodes[m].get("unit"), 0)
            for w in graph[m]:
                j = comp_of.get(w)
                if j is not None and j != k:
                    bits |= cbits[j]
        cbits.append(bits)
    return ubit, {x: cbits[comp_of[x]] for x in graph}


def realized_errors(nodes, g, units, deps_all, full_carriers, only=None):
    """The `realized` part of check(): for each unit (of `only`, default all) whose realized fields are filled, its
    realizing nodes exist, its statement and steps are carried, and the units it cites are reached from those nodes."""
    errs = []
    ubit, nbits = unit_bits(nodes, g, units, deps_all)
    for u, rec in units.items():
        if only is not None and u not in only:
            continue
        r = rec.get("realized") or {}
        if not (r.get("statement") or any(r.get("steps", []))):
            continue
        for x in r.get("statement", []) + [y for s in r.get("steps", []) for y in s]:
            if x not in nodes:
                errs.append(f"units: {u} is realized by {x}, no such node")
        if not r.get("statement"):
            errs.append(f"units: {u} has steps realized but no node for its statement")
        for k, s in enumerate(r.get("steps", []), 1):
            if not s:
                errs.append(f"units: {u} step {k} is carried by no node")
        # the units it cites are reached from its realizing nodes
        start = [x for x in r.get("statement", []) + [y for s in r.get("steps", []) for y in s] if x in g.live]
        need = {v for v in rec.get("uses", []) if v in units}
        got = 0
        for x in start:
            got |= nbits.get(x, 0)
        if all(got & ubit[v] for v in need):
            continue
        # some cited unit is not reached by unit stamps: the whole reach decides through the fully realized units
        reach, st = set(), list(start)
        while st:
            x = st.pop()
            if x in reach:
                continue
            reach.add(x); st.extend(y for y in deps_all(x) if y not in reach)
        hit = {nodes[x].get("unit") for x in reach if x in nodes}
        # A sketch may be expanded by nodes located in a different blueprint unit.
        # Preserve their source-based unit stamp and honor the explicit binding only
        # when the entire statement and every proof step have been reached.
        for v, carriers in full_carriers:
            if carriers <= reach:
                hit.add(v)
        for v in rec.get("uses", []):
            if v in units and v not in hit:
                errs.append(f"units: {u} cites {v}, which its nodes do not reach")
    return errs


def check(nodes=None, verbose=True) -> list[str]:
    nodes = nodes or dq.load(); units, chapters = load_units()
    errs, info, tools_accepted = [], collections.Counter(), collections.Counter()
    g = dq.Dag(nodes)
    _dall = {}       # fastland: g.deps(x, "all") per node, computed once

    def deps_all(x):
        r = _dall.get(x)
        if r is None:
            r = _dall[x] = g.deps(x, "all")
        return r
    # fastland: the units whose statement and every step are realized, with their carrier nodes, computed once
    full_carriers = []
    for v, vrec in units.items():
        vr = vrec.get("realized") or {}
        statements, steps = vr.get("statement") or [], vr.get("steps") or []
        if not statements or len(steps) != len(vrec.get("steps") or []) or not all(steps):
            continue
        full_carriers.append((v, set(statements + [x for step in steps for x in step])))
    for i, d in g.live.items():
        if d.get("chapter") not in chapters:
            errs.append(f"units: {i} has no chapter ({d.get('chapter')!r})")
        if d.get("unit") is not None and d.get("unit") not in units:
            errs.append(f"units: {i} names a unit that does not exist: {d.get('unit')!r}")
    errs += realized_errors(nodes, g, units, deps_all, full_carriers)
    # nodes: proof dependencies leaving the route. The route is about proofs: a step of a statement in unit U may use a
    # statement (not a Mathlib leaf, not a definition: those are notions) only from U or a unit U cites, transitively.
    # A unit with no proof and no `uses` (a remark or an assembly) constrains nothing.
    _closure, _skip = {}, {}   # pfinc 2026-10-17 (cpu): per unit / per cited node, computed once
    for i, d in g.live.items():
        u, ch = d.get("unit"), d.get("chapter")
        if not u or dq.is_def(d) or u not in units:
            continue
        if not units[u].get("uses") and not units[u].get("steps"):
            continue
        allowed = _closure.get(u)
        if allowed is None:
            allowed = _closure[u] = closure(units, u)
        for c in g.deps(i, "proof"):
            sk = _skip.get(c)
            if sk is None:
                sk = _skip[c] = c not in g.live or dq.is_def(nodes[c]) or dq.is_leaf(nodes[c]) or dq.finished(nodes[c])
            if sk:
                continue
            cu, cc = nodes[c].get("unit"), nodes[c].get("chapter")
            ok = cu in allowed if cu else True
            if not ok:
                if c in (d.get("tool_uses") or []):
                    tools_accepted[i] += 1
                    continue
                split = str(d.get("status")) in ("split", "mathlib") and d.get("reviewed")
                msg = f"route: {i} ({u}) depends on {c} ({cu or cc}), outside its unit's route"
                if split:
                    errs.append(msg)
                else:
                    info[u] += 1
    if verbose:
        for e in errs:
            print(e)
        print(f"units: {len(units)} units, {len(chapters)} chapters; {len(errs)} errors; "
              f"{sum(info.values())} route departures in imported (unreviewed) nodes across {len(info)} units; "
              f"{sum(tools_accepted.values())} tool uses accepted by the lead on {len(tools_accepted)} nodes")
    return errs


def main() -> int:
    cmd = sys.argv[1] if len(sys.argv) > 1 else "check"
    if cmd == "build":
        parser = argparse.ArgumentParser(description="Build blueprint unit metadata")
        parser.add_argument("--snapshot", default="master")
        parser.add_argument("--unit", action="append", dest="selected")
        args = parser.parse_args(sys.argv[2:])
        if pathlib.Path(args.snapshot).name != args.snapshot or args.snapshot in (".", ".."):
            parser.error("--snapshot must name a directory under literature/blueprint")
        try:
            build(ROOT / "literature/blueprint" / args.snapshot / "blueprint", set(args.selected) if args.selected else None)
        except ValueError as e:
            parser.error(str(e))
        return 0
    if cmd == "route":
        for k, u, ch in route():
            print(f"{k}\t{u}\t{ch}")
        return 0
    if cmd == "check":
        return 1 if check() else 0
    print(__doc__); return 2


if __name__ == "__main__":
    sys.exit(main())
