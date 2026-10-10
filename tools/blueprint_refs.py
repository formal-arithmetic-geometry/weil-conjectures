#!/usr/bin/env python3
"""The `blueprint` field of every node: which node of the existing blueprint a DAG node is, comes from, or states again
(stages/1-dag.md §6, rule of the human of 2026-10-10).

Usage:
  tools/blueprint_refs.py backfill        fill the field mechanically on every node that lacks it or whose `from.place` is
                                          still "unspecified"; never overwrites what a worker or lead wrote
  tools/blueprint_refs.py index           write the reverse index coord/blueprint-index.tsv and print the two numbers
                                          kept in coord/STATE.md (also run by `tools/queue.py write`)
  tools/blueprint_refs.py check [ids]     print the field errors of all nodes (or of the given ids, strictly)
  tools/blueprint_refs.py search WORD...  the blueprint nodes (all chapters, also outside the reach) whose title, statement
                                          or source contain every WORD (case-insensitive); a word like 01YE is a tag
  tools/blueprint_refs.py ancestor ID     the blueprint node and place a node created for item ID gets in `from`

The field:
  "blueprint": {
    "is":      the blueprint node this node is: its own id for a node imported from the blueprint (one that carries
               `blueprint_kind`), else null;
    "from":    null for an imported node; for a node created in a split:
               {"node": the nearest blueprint ancestor, found by following `created.item` (null if the chain is broken),
                "place": the step, clause or sentence of that blueprint node's proof which this node states or makes
                         precise; "unspecified" when it could not be read off (the next worker who touches the node fills it),
                "via":   the created nodes between this node and the ancestor, nearest first ([] when created for it)};
    "same_as": blueprint nodes anywhere in the blueprint (any chapter, also outside the reach) that state the same thing in
               another form, found by search; [] when the search found none; null when nobody has searched yet
  }

The backfill reads `place` off the ancestor's own split: the steps of the ancestor whose `uses` contain the head of the chain
(with the step's `source.place` when the step has one), else "statement" when the ancestor's statement cites it, else
"pointer" when the ancestor points to it.
"""
from __future__ import annotations
import collections, datetime, json, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
NODES = ROOT / "dag" / "nodes"
INDEX = ROOT / "coord" / "blueprint-index.tsv"
UNSPEC = "unspecified"
KEYS = ("is", "from", "same_as")


def load() -> tuple[dict[str, dict], dict[str, pathlib.Path]]:
    nodes, paths = {}, {}
    for p in sorted(NODES.rglob("*.json")):
        try:
            d = json.loads(p.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        if isinstance(d, dict) and d.get("id"):
            nodes[str(d["id"])] = d; paths[str(d["id"])] = p
    return nodes, paths


def is_bp(d: dict) -> bool:
    return "blueprint_kind" in d


def chain(i: str, nodes: dict[str, dict]) -> tuple[str | None, list[str]]:
    """Follow created.item from node i to the nearest blueprint node; return (ancestor, chain of created nodes from i up)."""
    seen, cur, path = set(), i, []
    while True:
        d = nodes.get(cur)
        if d is None or cur in seen:
            return None, path
        seen.add(cur)
        if is_bp(d) and cur != i:
            return cur, path
        path.append(cur)
        it = (d.get("created") or {}).get("item")
        if not it:
            return None, path
        cur = str(it)


def read_place(anc: dict, head: str) -> str:
    steps = [k for k, s in enumerate(anc.get("proof") or [], 1) if isinstance(s, dict) and head in (s.get("uses") or [])]
    if steps:
        out = "step " + ", ".join(map(str, steps)) + " of its split"
        sp = (anc["proof"][steps[0] - 1].get("source") or {}) if isinstance(anc["proof"][steps[0] - 1].get("source"), dict) else {}
        if sp.get("place"):
            out += f" (source: {str(sp['place'])[:160]})"
        return out
    if head in (anc.get("stmt_deps") or []):
        return "its statement (a notion the statement uses)"
    if any(isinstance(p, dict) and p.get("to") == head for p in (anc.get("pointers") or [])):
        return "a pointer of its statement (well-definedness of the definition)"
    return UNSPEC


def computed(i: str, nodes: dict[str, dict]) -> dict:
    d = nodes[i]
    if is_bp(d):
        return {"is": i, "from": None, "same_as": None}
    anc, path = chain(i, nodes)
    if anc is None:
        return {"is": None, "from": {"node": None, "place": UNSPEC, "via": path[1:]}, "same_as": None}
    head = path[-1]  # the created node directly created for the ancestor
    return {"is": None, "from": {"node": anc, "place": read_place(nodes[anc], head), "via": path[1:]}, "same_as": None}


def ancestor_for_item(item: str, nodes: dict[str, dict]) -> str | None:
    """The `from.node` of a node created for `item`."""
    d = nodes.get(item)
    if d is None:
        return None
    if is_bp(d):
        return item
    return chain(item, nodes)[0]


def with_field(d: dict, field: dict) -> dict:
    out = {}
    for k, v in d.items():
        if k == "blueprint":
            continue
        out[k] = v
        if k == "id":
            out["blueprint"] = field
    if "blueprint" not in out:
        out["blueprint"] = field
    return out


def backfill() -> int:
    nodes, paths = load()
    changed = filled = places = 0
    for i, d in nodes.items():
        new = computed(i, nodes)
        cur = d.get("blueprint")
        if isinstance(cur, dict) and all(k in cur for k in KEYS):
            f = dict(cur)
            f["is"] = new["is"]  # mechanical truth
            if is_bp(d):
                f["from"] = None
            elif not isinstance(f.get("from"), dict) or not f["from"].get("node") and new["from"]["node"]:
                f["from"] = new["from"]
            elif f["from"].get("place") in (None, "", UNSPEC) and new["from"]["place"] != UNSPEC and f["from"].get("node") == new["from"]["node"]:
                f["from"] = {**f["from"], "place": new["from"]["place"]}; places += 1
            if f == cur:
                continue
        else:
            f = new; filled += 1
        nodes[i] = with_field(d, f)
        paths[i].write_text(json.dumps(nodes[i], ensure_ascii=False, indent=1) + "\n")
        changed += 1
    print(f"backfill: {changed} node files written ({filled} got the field, {places} got a place)")
    return 0


def errors(nodes: dict[str, dict], strict_ids: set[str] = frozenset()) -> list[str]:
    """Field errors. Every node: the field exists and is well formed. Strict (new nodes and the item of a split): `from.place`
    is not "unspecified" and `same_as` is a list (the search was made)."""
    bps = {i for i, d in nodes.items() if is_bp(d)}
    out = []
    for i, d in nodes.items():
        f = d.get("blueprint")
        if not isinstance(f, dict) or any(k not in f for k in KEYS):
            out.append(f"blueprint: {i} has no blueprint field with is, from, same_as (tools/blueprint_refs.py; stages/1-dag.md §6)")
            continue
        if i in bps:
            if f.get("is") != i:
                out.append(f"blueprint: {i} is imported from the blueprint but blueprint.is is {f.get('is')!r}")
            if f.get("from") is not None:
                out.append(f"blueprint: {i} is imported from the blueprint; blueprint.from must be null")
        else:
            if f.get("is") is not None:
                out.append(f"blueprint: {i} is not a blueprint node; blueprint.is must be null")
            fr = f.get("from")
            if not isinstance(fr, dict) or "node" not in fr or not isinstance(fr.get("place"), str) or not fr.get("place"):
                out.append(f"blueprint: {i}: blueprint.from must be {{node, place, via}}")
            elif fr.get("node") is not None and fr["node"] not in bps:
                out.append(f"blueprint: {i}: blueprint.from.node {fr['node']} is not a blueprint node")
            elif i in strict_ids and fr.get("place") == UNSPEC:
                out.append(f"blueprint: {i}: blueprint.from.place is unspecified; name the step, clause or sentence of {fr.get('node')}'s proof this node serves")
        sa = f.get("same_as")
        if sa is not None:
            if not isinstance(sa, list):
                out.append(f"blueprint: {i}: blueprint.same_as must be a list of blueprint node ids (or null before the search)")
            else:
                for s in sa:
                    if s not in bps or s == i:
                        out.append(f"blueprint: {i}: blueprint.same_as names {s!r}, which is not another blueprint node")
        elif i in strict_ids and i not in bps:
            out.append(f"blueprint: {i}: blueprint.same_as is null; search the whole blueprint (tools/blueprint_refs.py search) and write the result ([] if none)")
    return out


def reach() -> set[str]:
    sys.path.insert(0, str(ROOT / "tools"))
    import dag_queue as dq  # noqa: E402
    g = dq.Dag(dq.load())
    return set(g.dist)


def index(write: bool = True) -> tuple[int, int, int]:
    nodes, _ = load()
    rch = reach()
    bps = sorted(i for i, d in nodes.items() if is_bp(d))
    is_of, from_of, same_of = collections.defaultdict(list), collections.defaultdict(list), collections.defaultdict(list)
    same_count = 0
    for i, d in nodes.items():
        f = d.get("blueprint") or {}
        if f.get("is"):
            is_of[f["is"]].append(i)
        fr = f.get("from")
        if isinstance(fr, dict) and fr.get("node"):
            from_of[fr["node"]].append(i)
        if isinstance(f.get("same_as"), list) and f["same_as"]:
            if not is_bp(d):
                same_count += 1
            for s in f["same_as"]:
                same_of[s].append(i)
    on = [b for b in bps if b in rch]
    served = sum(1 for b in on if from_of.get(b))
    if write:
        lines = [
            f"# reverse index blueprint node -> DAG nodes; generated by tools/blueprint_refs.py index (and tools/queue.py write) on {datetime.datetime.now(datetime.timezone.utc):%Y-%m-%d %H:%M} UTC",
            f"# blueprint nodes on the reach with at least one DAG node from their proof: {served} of {len(on)}; new nodes found the same as a blueprint node: {same_count}",
            "blueprint_id\tchapter\tunit\ton_reach\tstatus\tis\tfrom\tsame_as",
        ]
        for b in bps:
            d = nodes[b]
            lines.append("\t".join([b, str(d.get("chapter") or ""), str(d.get("unit") or ""), "1" if b in rch else "0", str(d.get("status") or ""),
                                    ",".join(sorted(is_of.get(b, []))), ",".join(sorted(from_of.get(b, []))), ",".join(sorted(same_of.get(b, [])))]))
        INDEX.write_text("\n".join(lines) + "\n")
    return served, len(on), same_count


def search(words: list[str]) -> int:
    nodes, _ = load()
    ws = [w.lower() for w in words]
    hits = 0
    for i, d in sorted(nodes.items()):
        if not is_bp(d):
            continue
        hay = " ".join([i, str(d.get("title") or ""), str(d.get("statement") or ""), json.dumps(d.get("source"), ensure_ascii=False),
                        " ".join(map(str, d.get("blueprint_tags") or []))]).lower()
        if all(w in hay for w in ws):
            hits += 1
            print(f"{i}\t{d.get('chapter')}\t{d.get('status')}\t{re.sub(r'\\s+', ' ', str(d.get('statement') or ''))[:220]}")
    print(f"{hits} blueprint nodes match {' '.join(words)!r}")
    return 0


def main() -> int:
    a = sys.argv[1:]
    if not a:
        print(__doc__); return 2
    if a[0] == "backfill":
        return backfill()
    if a[0] == "index":
        s, n, c = index()
        print(f"blueprint nodes on the reach with at least one DAG node from their proof: {s} of {n}; new nodes the same as a blueprint node: {c}; wrote {INDEX.relative_to(ROOT)}")
        return 0
    if a[0] == "check":
        nodes, _ = load()
        errs = errors(nodes, set(a[1:]))
        if a[1:]:
            errs = [e for e in errs if any(f" {i}" in e or f"{i}:" in e for i in a[1:])]
        for e in errs:
            print(e)
        print(f"{len(errs)} blueprint field errors")
        return 1 if errs else 0
    if a[0] == "search":
        return search(a[1:])
    if a[0] == "ancestor" and len(a) == 2:
        nodes, _ = load()
        anc = ancestor_for_item(a[1], nodes)
        print(f"a node created for {a[1]} has blueprint.from.node = {anc}")
        return 0
    print(__doc__); return 2


if __name__ == "__main__":
    sys.exit(main())
