#!/usr/bin/env python3
"""Import direction between the upstream library (WeilConjectures, Weil) and the project's modules (Sheaf), when both
are roots of the one package lean/ (stage-3 layout, prepared on branch stage3-prep).

Rule: an upstream module U may import a Sheaf module S only if U is not in the import closure of S (otherwise the
import closes a cycle). The modules "below Sheaf" are the upstream modules some Sheaf module reaches; a Sheaf import
added to one of them is a cycle exactly when that Sheaf module reaches it back.

Usage:
  tools/import_direction.py check          whole graph: cycles (must be none), what Sheaf imports from upstream,
                                           the upstream modules below Sheaf, and the upstream modules importing Sheaf
  tools/import_direction.py may <U> <S>    may upstream module U import Sheaf module S? (exit 0 yes, 3 no)
Reads sources only; parses `[public] [meta] import [all] M` (the module-system forms).
"""
from __future__ import annotations
import pathlib, re, sys
ROOT = pathlib.Path(__file__).resolve().parent.parent / "lean"
IMP = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.']+)", re.M)
SRC = [("WeilConjectures", ROOT), ("Sheaf", ROOT), ("Weil", ROOT / "Comparator")]


def strip_comments(s: str) -> str:
    s = re.sub(r"/-.*?-/", " ", s, flags=re.S)  # imports sit above any nested comment; good enough for headers
    return re.sub(r"--[^\n]*", " ", s)


def graph():
    g = {}
    for root, base in SRC:
        files = list((base / root).rglob("*.lean")) + ([base / f"{root}.lean"] if (base / f"{root}.lean").is_file() else [])
        for p in files:
            m = ".".join(p.relative_to(base).with_suffix("").parts)
            head = strip_comments(p.read_text(errors="ignore")).split("\nsection", 1)[0]
            g[m] = set(IMP.findall(head))
    tc = ROOT / "TargetsCheck.lean"
    if tc.is_file():
        g["TargetsCheck"] = set(IMP.findall(strip_comments(tc.read_text())))
    return g


def closure(m, g, memo):
    if m in memo:
        return memo[m]
    memo[m] = set()
    out = set()
    for i in g.get(m, ()):
        if i in g:
            out.add(i); out |= closure(i, g, memo)
    memo[m] = out
    return out


def cycles(g):
    sys.setrecursionlimit(100000)
    idx, low, st, on, out, n = {}, {}, [], set(), [], [0]
    def sc(v):
        idx[v] = low[v] = n[0]; n[0] += 1; st.append(v); on.add(v)
        for w in g.get(v, ()):
            if w not in g: continue
            if w not in idx: sc(w); low[v] = min(low[v], low[w])
            elif w in on: low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            comp = []
            while True:
                w = st.pop(); on.discard(w); comp.append(w)
                if w == v: break
            if len(comp) > 1 or v in g.get(v, ()): out.append(comp)
    for v in g:
        if v not in idx: sc(v)
    return out


def up(m): return m.split(".")[0] in ("WeilConjectures", "Weil")


def main():
    g = graph(); memo = {}
    if sys.argv[1:2] == ["may"] and len(sys.argv) == 4:
        u, s = sys.argv[2], sys.argv[3]
        if u in closure(s, g, memo) or u == s:
            print(f"NO: {s} already reaches {u}; importing it from {u} closes a cycle"); return 3
        print(f"yes: {s} does not reach {u}"); return 0
    if sys.argv[1:] != ["check"]:
        print(__doc__); return 2
    sheaf = [m for m in g if m.startswith("Sheaf.")]
    direct = {i for s in sheaf for i in g[s] if up(i)}
    below = set()
    for s in sheaf:
        below |= {x for x in closure(s, g, memo) if up(x)}
    ups = [m for m in g if up(m)]
    up_imp_sheaf = sorted(m for m in ups if any(i.startswith("Sheaf.") for i in g[m]))
    cyc = cycles(g)
    print(f"modules: upstream {len(ups)}, Sheaf {len(sheaf)}")
    print(f"Sheaf modules importing upstream directly: {sum(1 for s in sheaf if any(up(i) for i in g[s]))}; "
          f"distinct upstream modules imported directly: {len(direct)}; upstream modules below Sheaf (closure): {len(below)}")
    print(f"upstream modules importing a Sheaf module: {len(up_imp_sheaf)}" + (": " + " ".join(up_imp_sheaf[:20]) if up_imp_sheaf else ""))
    print(f"import cycles: {len(cyc)}")
    for c in cyc[:10]:
        print("  cycle: " + " ".join(sorted(c)[:12]))
    return 1 if cyc else 0


if __name__ == "__main__":
    sys.exit(main())
