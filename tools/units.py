#!/usr/bin/env python3
"""The units and chapters of the blueprint, as records the tools can check (SETUP.md, the three levels; stages/1-dag.md §7).

Usage:
  tools/units.py build     write dag/chapters/<sec>.json (16) and dag/units/<sk>.json (389) from the blueprint, keeping the
                           `realized` fields already recorded, and stamp every node in dag/nodes/ with `chapter` and `unit`
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
"""
from __future__ import annotations
import collections, json, pathlib, re, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import dag_queue as dq  # noqa: E402

ROOT = dq.li.ROOT
BP = ROOT / "literature/blueprint/master/blueprint"
UNITS = ROOT / "dag/units"
CHAPTERS = ROOT / "dag/chapters"


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
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(d, ensure_ascii=False, indent=1) + "\n")


def build() -> None:
    old_units = {p.stem: json.loads(p.read_text()) for p in UNITS.glob("*.json")} if UNITS.is_dir() else {}
    nch = nun = 0
    for sec in sorted(BP.glob("sec-*")):
        fm, body = frontmatter((sec / "_section.md").read_text())
        key = re.search(r"key theorem:\s*(.*)", body)
        ref = re.search(r"reference:\s*(.*)", body)
        dump(CHAPTERS / f"{sec.name}.json", {
            "id": sec.name, "kind": "chapter", "title": fm.get("title"), "uses": fm.get("uses", []),
            "key_theorem": key.group(1).strip() if key else None, "reference": ref.group(1).strip() if ref else None,
            "text": body.strip(), "source": str((sec / "_section.md").relative_to(ROOT))})
        nch += 1
        for sk in sorted(sec.glob("sk-*")):
            f = sk / "_section.md"
            if not f.is_file():
                continue
            fm, body = frontmatter(f.read_text())
            stmt, _, proof = body.partition("\n## Proof")
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
    nodes = dq.load(); files = {p.stem: p for p in dq.nodes_dir().rglob("*.json")}
    units = {p.stem for p in UNITS.glob("*.json")}; chapters = {p.stem for p in CHAPTERS.glob("*.json")}

    def place(i, seen=()):
        d = nodes[i]
        doc = str((d.get("source") or {}).get("document") or "")
        m = re.search(r"blueprint/master/blueprint/(sec-[^/]+)/(?:(sk-[^/]+)/)?[^/]+\.md$", doc)
        if m and m.group(1) in chapters:
            return m.group(1), (m.group(2) if m.group(2) in units else None)
        item = (d.get("created") or {}).get("item")
        if item in nodes and item not in seen:
            return place(item, seen + (i,))
        return files[i].parent.name if files[i].parent.name in chapters else None, None

    n = 0
    for i, d in nodes.items():
        ch, un = place(i)
        if d.get("chapter") != ch or d.get("unit") != un:
            d["chapter"], d["unit"] = ch, un
            files[i].write_text(json.dumps(d, ensure_ascii=False, indent=1) + "\n"); n += 1
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


def check(nodes=None, verbose=True) -> list[str]:
    nodes = nodes or dq.load(); units, chapters = load_units()
    errs, info, tools_accepted = [], collections.Counter(), collections.Counter()
    g = dq.Dag(nodes)
    for i, d in g.live.items():
        if d.get("chapter") not in chapters:
            errs.append(f"units: {i} has no chapter ({d.get('chapter')!r})")
        if d.get("unit") is not None and d.get("unit") not in units:
            errs.append(f"units: {i} names a unit that does not exist: {d.get('unit')!r}")
    # units: realized fields
    for u, rec in units.items():
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
        reach, st = set(), list(start)
        while st:
            x = st.pop()
            if x in reach:
                continue
            reach.add(x); st += g.deps(x, "all")
        hit = {nodes[x].get("unit") for x in reach if x in nodes}
        for v in rec.get("uses", []):
            if v in units and v not in hit:
                errs.append(f"units: {u} cites {v}, which its nodes do not reach")
    # nodes: proof dependencies leaving the route. The route is about proofs: a step of a statement in unit U may use a
    # statement (not a Mathlib leaf, not a definition: those are notions) only from U or a unit U cites, transitively.
    # A unit with no proof and no `uses` (a remark or an assembly) constrains nothing.
    for i, d in g.live.items():
        u, ch = d.get("unit"), d.get("chapter")
        if not u or dq.is_def(d) or u not in units:
            continue
        if not units[u].get("uses") and not units[u].get("steps"):
            continue
        allowed = closure(units, u)
        for c in g.deps(i, "proof"):
            if c not in g.live or dq.is_def(nodes[c]) or dq.is_leaf(nodes[c]) or dq.finished(nodes[c]):
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
        build(); return 0
    if cmd == "route":
        for k, u, ch in route():
            print(f"{k}\t{u}\t{ch}")
        return 0
    if cmd == "check":
        return 1 if check() else 0
    print(__doc__); return 2


if __name__ == "__main__":
    sys.exit(main())
