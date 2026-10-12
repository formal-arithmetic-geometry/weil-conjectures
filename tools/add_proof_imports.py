#!/usr/bin/env python3
"""The imports of a module are the plan for its proof (stages/2-statements.md §3, rule 7): add to every stated module
the import of the modules of its nodes' stated proof dependencies. Reads the DAG and the sources; no Lean is run.

Usage:
  tools/add_proof_imports.py --check [--json FILE]   print the imports that are missing and would be added, and the
                                                     ones left out with the reason; write nothing. Exit 1 if any is
                                                     missing, else 0. The maintainer runs it after each build.
  tools/add_proof_imports.py [--json FILE]           add them (run it as `flock coord/.merge.lock python3 tools/...`;
                                                     the tool takes no lock itself). Running it twice adds nothing new.
  options: --public   write `public import` instead of `import` (default: `import`, see below)
           --all      print every edge of every class, not the first 40

An edge is (M, D): a node whose `lean.module` is M lists in `proof_deps` a node whose `lean.module` is D, both files
of the library (`Sheaf.*`, `WeilConjectures.*`), M != D, and M does not import D directly. What happens to it:

  added        `import D` is written after the last import of M.
  proved       the node's own declaration in M has no `sorry` left: its proof exists, the plan is not needed, and the
               worker who proved it has removed the imports the proof did not use (stage 3 §2). Adding them again
               would undo the pruning, so a proved node gets none. (When the declaration cannot be found in M by name,
               the module counts as proved when it contains no `sorry` at all.)
  cycle        D already reaches M through imports, so the import would close a cycle. The node DAG is acyclic, but
               several nodes share a module and statement and proof edges mix (a lemma about a definition imports the
               module of the definition; a theorem of that module uses the lemma). Edges are taken nearest to a target
               first, each tested against the graph with the edges already taken; the ones left out are listed with a
               path D -> ... -> M. Their plan is used by moving the theorem out of M, never by forcing the import.
  upstream     M is a module of the source library (`WeilConjectures.*`) that the targets do not reach. A source module
               gets imports only while the targets reach it (through the imports as they are after this run, computed
               to a fixed point) and its node is not proved; every other source file stays as upstream has it.
  reserved     M is one of the two target modules another team proves (RESERVED below): never touched.
  no file      D is recorded in the node but lean/ has no such file.
  excluded     the edge is listed in tools/proof_imports_skip.tsv (`M<tab>D<tab>reason`): an import that was tried and
               breaks M for a reason other than a cycle. The list is empty unless a build has shown such a case.

The import is written `import D`, without `public`: only the proof needs it, no module importing M sees it, so the
names of D reach no other file, a later removal by the worker who proves M is a proof-only delivery (review class
AUTO), and a change in D recompiles M and nothing above M.
"""
from __future__ import annotations
import collections, json, pathlib, re, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import leanindex as li  # noqa: E402

ROOTS = ("Sheaf.", "WeilConjectures.")
RESERVED = {
    "WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine",
    "WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty",
}
SKIP = pathlib.Path(__file__).resolve().parent / "proof_imports_skip.tsv"
_IMPORT_LINE = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?[\w.']+")


def load_nodes() -> dict:
    out = {}
    for p in sorted((li.ROOT / "dag" / "nodes").glob("*/*.json")):
        try:
            d = json.loads(p.read_text())
        except (OSError, ValueError):
            continue
        if isinstance(d, dict) and d.get("id"):
            out[d["id"]] = d
    return out


def resolve(i: str, nodes: dict):
    """The node `i` stands for, following `merged_into`."""
    seen = set()
    while i in nodes and i not in seen and nodes[i].get("merged_into"):
        seen.add(i); i = str(nodes[i]["merged_into"])
    return nodes.get(i)


def module_of_node(d) -> str | None:
    l = d.get("lean") if d else None
    m = l.get("module") if isinstance(l, dict) else None
    return m if isinstance(m, str) and m.startswith(ROOTS) else None


class Sources:
    def __init__(self):
        self.text, self.cmds = {}, {}

    def read(self, mod: str) -> str | None:
        if mod not in self.text:
            p = li.file_of(mod)
            self.text[mod] = p.read_text(errors="ignore") if p.is_file() else None
        return self.text[mod]

    def proved(self, mod: str, node: dict) -> bool:
        """Has the node's own declaration in `mod` no `sorry` left?"""
        text = self.read(mod) or ""
        if li.sorry_count(text) == 0:
            return True
        l = node["lean"]
        names = {str(x) for x in [l.get("declaration")] + list(l.get("declarations") or []) if x}
        if mod not in self.cmds:
            try:
                self.cmds[mod] = li.commands(text)
            except Exception:  # a source the reader cannot split into commands: judged by the module
                self.cmds[mod] = []
        found = [c for c in self.cmds[mod] if c["name"] and c["name"] in names]
        if not found:
            return False  # the module has a sorry and the declaration is not found by name: not known to be proved
        return all(li.sorry_count(c["text"]) == 0 for c in found)


def path(g: dict, a: str, b: str):
    """A path of imports a -> ... -> b, or None."""
    prev, stack = {a: None}, [a]
    while stack:
        x = stack.pop()
        if x == b:
            out = []
            while x is not None:
                out.append(x); x = prev[x]
            return out[::-1]
        for y in g.get(x, ()):
            if y not in prev and y in g:
                prev[y] = x; stack.append(y)
    return None


def distances(g: dict) -> dict:
    dist, dq = {}, collections.deque()
    for r in sorted(g.get("TargetsCheck", ())):
        if r in g:
            dist[r] = 0; dq.append(r)
    while dq:
        x = dq.popleft()
        for y in g.get(x, ()):
            if y in g and y not in dist:
                dist[y] = dist[x] + 1; dq.append(y)
    return dist


def plan():
    """Returns (report, g): report maps a class to its edges [(M, D, [nodes of M], extra)], g is the import graph
    with the added edges."""
    nodes = load_nodes()
    _, imports = li.scan()
    g = {m: set(i) for m, i in imports.items()}
    src = Sources()
    want = collections.defaultdict(lambda: collections.defaultdict(set))   # M -> D -> nodes of M, unproved nodes only
    rep = collections.defaultdict(list)
    proved_edges = collections.defaultdict(set)
    counts = collections.Counter()
    for i, d in sorted(nodes.items()):
        m = module_of_node(d)
        if not m or d.get("merged_into") or m not in g:
            continue
        deps = d.get("proof_deps") or []
        cand = []
        for j in deps:
            dm = module_of_node(resolve(str(j), nodes))
            if not dm or dm == m:
                continue
            counts["edges between stated modules (node level)"] += 1
            if dm in g[m]:
                counts["of these, imported directly"] += 1; continue
            cand.append(dm)
        if not cand:
            continue
        is_proved = src.proved(m, d)
        for dm in cand:
            if dm not in g:
                rep["no file"].append((m, dm, [i], "")); continue
            if is_proved:
                proved_edges[(m, dm)].add(i)
            else:
                want[m][dm].add(i)
    for (m, dm), ids in sorted(proved_edges.items()):
        if dm not in want.get(m, {}):
            rep["proved"].append((m, dm, sorted(ids), ""))
    pending = {(m, dm) for m in want for dm in want[m]}
    if SKIP.is_file():
        for line in SKIP.read_text().splitlines():
            f = line.split("\t")
            if len(f) >= 2 and not line.startswith("#") and (f[0], f[1]) in pending:
                pending.discard((f[0], f[1]))
                rep["excluded"].append((f[0], f[1], sorted(want[f[0]][f[1]]), f[2] if len(f) > 2 else ""))
    for m, dm in sorted(pending):
        if m in RESERVED:
            rep["reserved"].append((m, dm, sorted(want[m][dm]), "")); pending.discard((m, dm))
    # to a fixed point: a source module becomes eligible when the targets reach it through the edges already added
    while True:
        dist = distances(g)
        todo = sorted((dist.get(m, 10**6), m, dm) for m, dm in pending
                      if m.startswith("Sheaf.") or m in dist)
        if not todo:
            break
        for _, m, dm in todo:
            pending.discard((m, dm))
            p = path(g, dm, m)
            if p is not None:
                rep["cycle"].append((m, dm, sorted(want[m][dm]), " -> ".join(p))); continue
            g[m].add(dm)
            rep["added"].append((m, dm, sorted(want[m][dm]), ""))
    for m, dm in sorted(pending):
        rep["upstream"].append((m, dm, sorted(want[m][dm]), ""))
    rep["#counts"] = dict(counts)
    return rep, g


def write(added, public: bool) -> int:
    by = collections.defaultdict(list)
    for m, dm, _, _ in added:
        by[m].append(dm)
    for m, ds in sorted(by.items()):
        p = li.file_of(m)
        text = p.read_text()
        comment = [(a, b) for k, a, b in li.lex(text) if k in li.COMMENT_KINDS]
        lines, pos, last, mod_line = text.split("\n"), 0, None, None
        for n, line in enumerate(lines):
            start = pos + (len(line) - len(line.lstrip()))
            pos += len(line) + 1
            s = line.strip()
            if not s or any(a <= start < b for a, b in comment):
                continue
            if s == "module":
                mod_line = n
            elif _IMPORT_LINE.match(s):
                last = n
            elif s != "prelude":
                break
        kw = "public import" if public and mod_line is not None else "import"
        new = [f"{kw} {d}" for d in sorted(set(ds))]
        if last is not None:
            lines[last + 1:last + 1] = new
        elif mod_line is not None:
            lines[mod_line + 1:mod_line + 1] = [""] + new
        else:
            lines[0:0] = new + [""]
        tmp = p.with_name(p.name + ".imports-new")
        tmp.write_text("\n".join(lines))
        tmp.replace(p)
    return len(by)


LABEL = {
    "added": "missing, to add",
    "cycle": "left out: the import would close a cycle (D -> ... -> M)",
    "proved": "not added: the node's declaration is proved (no sorry)",
    "upstream": "not added: module of the source library the targets do not reach",
    "reserved": "not added: target module another team proves",
    "no file": "not added: the dependency's module has no file",
    "excluded": "left out: listed in tools/proof_imports_skip.tsv",
}


def main() -> int:
    args = sys.argv[1:]
    check, public, every = "--check" in args, "--public" in args, "--all" in args
    jf = args[args.index("--json") + 1] if "--json" in args else None
    if set(args) - {"--check", "--public", "--all", "--json", jf}:
        print(__doc__); return 2
    rep, g = plan()
    c = rep.pop("#counts")
    print(f"proof-dependency edges between stated modules (node level): {c.get('edges between stated modules (node level)', 0)}; "
          f"imported directly: {c.get('of these, imported directly', 0)}")
    for k in ("added", "cycle", "excluded", "proved", "upstream", "reserved", "no file"):
        e = rep.get(k, [])
        print(f"{LABEL[k]}: {len(e)} imports in {len({m for m, _, _, _ in e})} modules")
        if k in ("added", "cycle", "excluded") or every:
            for m, dm, ids, extra in (e if every or k != "added" else e[:40]):
                print(f"  {m} <- {dm}   ({', '.join(ids[:3])})" + (f"   {extra}" if extra else ""))
            if not every and k == "added" and len(e) > 40:
                print(f"  ... and {len(e) - 40} more (--all)")
    added = rep.get("added", [])
    up = sorted({m for m, _, _, _ in added if m.startswith("WeilConjectures.")})
    print(f"modules of the source library that get imports: {len(up)}" + (": " + " ".join(up) if up else ""))
    if jf:
        pathlib.Path(jf).write_text(json.dumps({k: [list(x) for x in v] for k, v in rep.items()}, indent=1))
    if check:
        return 1 if added else 0
    # no cycle may exist after the edges are added: tested once more on the whole graph before anything is written
    for m, dm, _, _ in added:
        g[m].discard(dm)
        if path(g, dm, m) is not None:
            print(f"internal error: {m} <- {dm} would close a cycle; nothing written"); return 3
        g[m].add(dm)
    n = write(added, public)
    print(f"wrote {len(added)} imports into {n} files" + (" (public import)" if public else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
