#!/usr/bin/env python3
"""What a newer commit of the source library changes for us, read from two sorry maps (tools/sorry_map.lean).

Usage:
  tools/upstream_report.py <old map> <new map> [--json OUT] [--queue-before coord/queue.tsv copy]

Prints, and writes to OUT:
  - declarations of the old and of the new map; added, removed;
  - `sorry`s the source closed: declarations that contained `sorry` in the old map and exist without it in the new
    one. Of these: how many are in a module the targets reach (tools/queue.py analyse), how many are declarations of
    a DAG node (`lean`, `lean_audit.<branch>.decls`), how many are in a module that is a stage-3 item of the queue
    given by --queue-before (default coord/queue.tsv as it is), and how many we had proved ourselves in lean/
    (the source text here no longer has `sorry` in that declaration's lines: the count is by module, approximate);
  - `sorry`s the source added (new declarations with `sorry`, old ones that got one);
  - overlap candidates, for the rule "one definition per notion" (coord/upstream-overlaps.md): a declaration of
    lean/Sheaf whose full name, or whose last name component of at least 6 characters, is that of a declaration the
    source added. A full-name match is a clash; a last-component match is read by a person or an agent, who decides
    whether the two state the same notion.
Reads only.
"""
from __future__ import annotations
import collections, gzip, json, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|public|unsafe|partial|nonrec|scoped|local)\s+)*"
                  r"(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\s+([^\s({\[:]+)")


def load(path):
    op = gzip.open if str(path).endswith(".gz") else open
    own = {}
    with op(path, "rt") as fh:
        for l in fh:
            r = json.loads(l)
            o = own.setdefault(r["o"], {"sorry": False, "module": None, "kind": None, "l1": 0, "l2": 0})
            o["sorry"] |= bool(r["s"] or r["ts"])
            if r["n"] == r["o"]:
                o.update(module=r["m"], kind=r["k"], l1=r["l1"], l2=r["l2"])
    return own


def sheaf_decls():
    out = collections.defaultdict(list)                      # full name -> [module]
    for q in sorted((ROOT / "lean" / "Sheaf").rglob("*.lean")):
        mod = ".".join(q.relative_to(ROOT / "lean").with_suffix("").parts)
        ns = []
        for l in q.read_text(errors="ignore").split("\n"):
            s = l.strip()
            if s.startswith("namespace ") and len(s.split()) > 1: ns.append(s.split()[1])
            elif s.startswith("end ") and ns and len(s.split()) > 1 and s.split()[1] == ns[-1]: ns.pop()
            elif (m := DECL.match(l)):
                n = m.group(2)
                if m.group(1) == "instance" and n in (":", ""): continue
                out[n[7:] if n.startswith("_root_.") else ".".join(ns + [n])].append(mod)
    return out


def main():
    a = sys.argv[1:]
    if len(a) < 2:
        sys.exit(__doc__)
    opt = dict(zip(a[2::2], a[3::2]))
    old, new = load(a[0]), load(a[1])
    added = {n for n in new if n not in old}
    removed = {n for n in old if n not in new}
    closed = sorted(n for n, r in old.items() if r["sorry"] and n in new and not new[n]["sorry"])
    gone_sorry = sorted(n for n, r in old.items() if r["sorry"] and n not in new)
    opened = sorted(n for n, r in new.items() if r["sorry"] and not (n in old and old[n]["sorry"]))
    import queue as q
    _, dist = q.analyse()
    node_of = collections.defaultdict(set)
    for p in (ROOT / "dag" / "nodes").glob("*/*.json"):
        try: n = json.loads(p.read_text())
        except Exception: continue
        l = n.get("lean") if isinstance(n.get("lean"), dict) else {}
        names = [l.get("declaration")] + list(l.get("declarations") or [])
        audit = n.get("lean_audit")
        for br in (audit if isinstance(audit, dict) else {}).values():
            if isinstance(br, dict):
                names += [d.get("name") for d in br.get("decls") or [] if isinstance(d, dict)]
        for d in names:
            d = d.get("name") if isinstance(d, dict) else d
            if d: node_of[d].add(n.get("id", p.stem))
    qp = pathlib.Path(opt.get("--queue-before", ROOT / "coord" / "queue.tsv"))
    items = {l.split("\t")[0] for l in qp.read_text().splitlines() if l.split("\t")[1:2] == ["3"]} if qp.exists() else set()
    import leanindex as li
    def ours_proved(n):
        r = old[n]; p = ROOT / "lean" / (r["module"].replace(".", "/") + ".lean")
        return p.is_file() and li.sorry_count(p.read_text(errors="ignore")) == 0
    rows = [{"declaration": n, "module": new[n]["module"], "in_closure": new[n]["module"] in dist,
             "nodes": sorted(node_of.get(n, ())), "queue_item": new[n]["module"] in items} for n in closed]
    sd = sheaf_decls()
    last = collections.defaultdict(list)
    for n in added:
        if new[n]["kind"] in ("ctor", "rec"): continue
        last[n.split(".")[-1]].append(n)
    overlaps = []
    for n, mods in sorted(sd.items()):
        c = n.split(".")[-1]
        if n in added:
            overlaps.append({"ours": n, "module": mods[0], "upstream": [n], "match": "full name"})
        elif len(c) >= 6 and c in last and len(last[c]) <= 4:
            overlaps.append({"ours": n, "module": mods[0], "upstream": sorted(last[c]), "match": "last component"})
    rep = {"old": len(old), "new": len(new), "added": len(added), "removed": len(removed),
           "sorry_old": sum(r["sorry"] for r in old.values()), "sorry_new": sum(r["sorry"] for r in new.values()),
           "closed": rows, "removed_with_sorry": gone_sorry, "opened": opened, "overlaps": overlaps}
    if "--json" in opt:
        pathlib.Path(opt["--json"]).write_text(json.dumps(rep, indent=1))
    print(f"declarations {len(old)} -> {len(new)} (added {len(added)}, removed {len(removed)}); with sorry {rep['sorry_old']} -> {rep['sorry_new']}")
    print(f"sorries the source closed: {len(closed)}; in a module the targets reach: {sum(r['in_closure'] for r in rows)}; "
          f"declarations of a DAG node: {sum(bool(r['nodes']) for r in rows)} ({len({i for r in rows for i in r['nodes']})} nodes); "
          f"in a stage-3 queue item: {sum(r['queue_item'] for r in rows)} ({len({r['module'] for r in rows if r['queue_item']})} modules)")
    for r in rows:
        if r["in_closure"] or r["nodes"] or r["queue_item"]:
            print(f"  {r['declaration']}  [{r['module']}]{' closure' if r['in_closure'] else ''}{' item' if r['queue_item'] else ''} {' '.join(r['nodes'])}")
    print(f"declarations with sorry the source removed or renamed: {len(gone_sorry)}; sorries the source added: {len(opened)} "
          f"({sum(1 for n in opened if new[n]['module'] in dist)} in a module the targets reach)")
    print(f"overlap candidates (lean/Sheaf declarations {len(sd)}): {len(overlaps)}; full-name: {sum(o['match'] == 'full name' for o in overlaps)}")
    for o in overlaps:
        print(f"  {o['match']:14} {o['ours']} ({o['module']})  ~  {', '.join(o['upstream'])}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
