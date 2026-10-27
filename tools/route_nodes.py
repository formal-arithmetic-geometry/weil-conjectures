#!/usr/bin/env python3
"""Route sorries without a DAG node get a maintainer stage-1 node (the human, 2026-10-23: every proof-related upstream
sorry gets a node; a node without a written proof goes to stage 1 to be stated in words and split).

A declaration on a batch's sorry route (local/sorry-route.json: "batches" and "own", minus what the batch assumes,
coord/assumed.tsv) that no node records (lean.declaration / lean.declarations) was only worked as a stage-3 module item,
skipping stage 1. For each such declaration this tool writes a provisional node:
  - statement: the declaration's docstring and Lean signature (provisional, created.why says so: the stage-1 worker
    writes it in words with [node] citations and stmt_deps, does the Mathlib searches and splits it);
  - lean: the existing declaration attached as it stands (existing true, proof still `sorry`);
  - parent (created.item, blueprint.from, chapter, unit): the node whose Lean uses it, best first: a node whose recorded
    declaration's text names it; a node of a module whose code names it; a node of the declaring module; a node of the
    nearest importing module. Among these, nodes the stage-1 walk reaches (and not finished) first. The new node is
    cited in the parent's proof_deps; if the stage-1 walk still does not reach it (the parent is finished or an unsplit
    node without its plan), its id goes to coord/preopen.txt so the queue lists it in stage 1 anyway.
Run by ~/cc1/sorry-route-loop.sh after each tools/sorry_route.py, before tools/queue.py write.

    python3 tools/route_nodes.py              dry run: print what would be created
    python3 tools/route_nodes.py --write      write the nodes (no commit)
    python3 tools/route_nodes.py --commit     write and commit under coord/.merge.lock (SHEAF_LEAD=L-only)
    --parent=DECL=NODE                        take NODE as the parent of DECL instead of the heuristic's choice
"""
import collections, datetime, fcntl, json, os, pathlib, re, subprocess, sys
R = pathlib.Path(__file__).resolve().parent.parent
os.chdir(R); sys.path.insert(0, str(R / "tools"))
import dag_queue as dq, leanindex as li, assumed, blueprint_refs as bp  # noqa: E402

ROUTE = R / "local" / "sorry-route.json"
PREOPEN = R / "coord" / "preopen.txt"
MATHLIB = R / "lean" / ".lake" / "packages" / "mathlib" / "Mathlib"
TODAY = datetime.date.today().isoformat()
KW = r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)"
CAP = 40
DEFKW = {"def", "abbrev", "structure", "class", "inductive", "opaque"}


def node_decls(d):
    l = d.get("lean") if isinstance(d.get("lean"), dict) else {}
    out = ([l["declaration"]] if l.get("declaration") else []) + list(l.get("declarations") or [])
    try:
        out += list(dq.decl_names(d))
    except Exception:
        pass
    return out


def missing_route_decls(nodes):
    """{declaration: {"module", "batches"}} for the route declarations no node records"""
    r = json.loads(ROUTE.read_text())
    rec = {x for d in nodes.values() for x in node_decls(d)} - PRETEND   # --pretend-missing=DECL: dry-run test only
    out = {}
    for key in ("batches", "own"):
        for b, mods in (r.get(key) or {}).items():
            skip = set(assumed.decls_for(b))
            for m, xs in mods.items():
                for x in xs:
                    if x in rec or x in skip:
                        continue
                    e = out.setdefault(x, {"module": m, "batches": set()})
                    e["batches"].add(b)
    return out


def source_file(m):
    p = li.file_of(m)
    if p.is_file():
        return p, False
    q = R / "quarantine" / pathlib.Path(*m.split(".")).with_suffix(".lean")
    return (q, True) if q.is_file() else (None, False)


def decl_block(text, short):
    """(docstring, declaration text up to its end, first line, last line), 1-based lines, or None"""
    lines = text.split("\n")
    head = re.compile(rf"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|public|nonrec|partial|unsafe)\s+)*"
                      rf"({KW})\s+(?:[\w.']*\.)?{re.escape(short)}(?![\w'.])")
    k = next((i for i, l in enumerate(lines) if head.match(l)), None)
    if k is None:
        return None
    kw = head.match(lines[k]).group(1)
    e = k + 1
    while e < len(lines) and (not lines[e].strip() or lines[e][0].isspace() or li._CONT.match(lines[e])):
        e += 1
    while e > k + 1 and not lines[e - 1].strip():
        e -= 1
    s, doc = k, ""
    j = k - 1
    while j >= 0 and (re.match(r"(?:@\[[^\]]*\]\s*$|set_option\b.*\sin\s*$|open\b.*\sin\s*$|omit\b.*\sin\s*$|--)", lines[j])):
        j -= 1
    if j >= 0 and lines[j].rstrip().endswith("-/"):
        i = j
        while i >= 0 and "/--" not in lines[i]:
            i -= 1
        if i >= 0:
            doc = "\n".join(lines[i:j + 1]).strip()
            doc = re.sub(r"^/--\s*|\s*-/$", "", doc).strip()
            s = i
    return doc, "\n".join(lines[k:e]), kw, s + 1, e


def slug(short):
    s = re.sub(r"(?<=[a-z0-9])(?=[A-Z])", "-", short).replace("_", "-").replace("'", "")
    return re.sub(r"-+", "-", s).lower().strip("-")


def candidates(x, mod, batches, nodes, g, bymod, users_cache, imports):
    """ranked parent candidates [(rank tuple, node id, how)]"""
    short = x.split(".")[-1]
    if "files" not in users_cache:
        users_cache["files"] = [p for p in li.library_files()]
    out = []
    ns = x.split(".")[:-1]
    occ = re.compile(rf"(?<![\w'])((?:[\w']+\.)*){re.escape(short)}(?![\w'])")

    class _Word:
        """an occurrence of the name, unqualified or qualified by a suffix of its namespace (Etale.foo is not
        CondensedRing.foo)"""
        @staticmethod
        def search(t):
            for mt in occ.finditer(t):
                q = [z for z in mt.group(1).split(".") if z]
                if not q or q == ns[len(ns) - len(q):]:
                    return True
            return False
    word = _Word

    def reach(i):
        d = nodes[i]
        return (0 if i in g.dist1 and not dq.finished(d) else 1 if i in g.dist else 2, g.dist.get(i, 10**6))

    seen = set()
    for p in users_cache["files"]:
        try:
            raw = p.read_text(errors="ignore")
        except OSError:
            continue
        if short not in raw:
            continue
        code = li.strip(raw)
        if not word.search(code):
            continue
        m = li.module_of(p)
        # a user imports the declaring module (Etale.smoothPurityIso is not CondensedRing.smoothPurityIso)
        if m != mod and mod not in li.closure(m, imports, users_cache.setdefault("closure", {})):
            continue
        cmds = {c["name"]: c["text"] for c in li.commands(raw) if c["name"]}
        if any(n != x and n.split(".")[-1] == short for n in cmds):
            continue   # the module declares its own namesake: its occurrences are ambiguous
        for i in bymod.get(m, ()):
            uses = any(n != x and word.search(cmds.get(n, "")) for n in node_decls(nodes[i]))
            if m == mod and not uses:
                continue
            tier = 0 if uses else 1
            out.append(((tier,) + reach(i), i, ("its declaration uses" if uses else f"its module {m} uses")))
            seen.add(i)
    for i in bymod.get(mod, ()):
        if i not in seen:
            out.append(((2,) + reach(i), i, f"declared in its module {mod}")); seen.add(i)
    if not out:
        users = collections.defaultdict(set)
        for m, imps in imports.items():
            for q in imps:
                users[q].add(m)
        level, done = {mod}, {mod}
        for depth in range(1, 6):
            level = {u for q in level for u in users.get(q, ())} - done
            done |= level
            hit = [(i, m) for m in sorted(level) for i in bymod.get(m, ())]
            if hit:
                out += [((3, depth) + reach(i), i, f"its module {m} imports {mod} ({depth} step{'s' if depth > 1 else ''})")
                        for i, m in hit]
                break
            if not level:
                break
    if not out:   # nothing in the library names or imports it (e.g. the users are quarantined): its batches' targets
        for b in sorted(batches):
            f = R / "coord" / f"nodes-{b}-targets.txt"
            f = f if f.exists() else R / "coord" / "new-targets.txt"
            ts = [l.split()[0] for l in (f.read_text().splitlines() if f.exists() else [])
                  if l.strip() and not l.lstrip().startswith("#")]
            out += [((4,) + reach(i), i, f"target of {b}, whose sorry route reaches it") for i in ts if i in nodes]
    return sorted(out)


def mathlib_grep(short):
    q = f"grep -rlw '{short}' lean/.lake/packages/mathlib/Mathlib/"
    try:
        r = subprocess.run(["grep", "-rlw", short, str(MATHLIB)], capture_output=True, text=True, timeout=120).stdout.split()
    except Exception:
        r = []
    r = [str(pathlib.Path(p).relative_to(MATHLIB.parent)) for p in r]
    return {"tool": "grep", "query": q, "results": ", ".join(r[:6]) if r else "none", "date": TODAY,
            "verdict": "no match" if not r else "name occurs; the stage-1 worker checks it",
            "note": "name grep by tools/route_nodes.py only; the stage-1 worker adds LeanSearch / Loogle / LeanFinder searches"}


def build(x, info, nodes, g, bymod, cache, imports):
    mod, short = info["module"], x.split(".")[-1]
    p, quarantined = source_file(mod)
    if p is None:
        return None, f"{x}: source of {mod} not found"
    blk = decl_block(p.read_text(errors="ignore"), short)
    if blk is None:
        return None, f"{x}: declaration {short} not found in {p.relative_to(R)}"
    doc, decl, kw, a, b = blk
    if not quarantined and li.sorry_count(decl) == 0:
        return None, f"{x}: sorry-free in live now (the route read an older published build); no node needed"
    cs = candidates(x, mod, info["batches"], nodes, g, bymod, cache, imports)
    if x in OVERRIDE and OVERRIDE[x] in nodes:   # --parent DECL=NODE (maintainer's choice)
        cs = [((-1,), OVERRIDE[x], "its Lean uses it (maintainer's choice)")] + [c for c in cs if c[1] != OVERRIDE[x]]
    if not cs:
        return None, f"{x}: no node uses it or its module (no parent found)"
    _, parent, how = cs[0]
    pd = nodes[parent]
    kind = "definition" if kw in DEFKW else "statement"
    base = ("def-route-" if kind == "definition" else "lem-route-") + slug(short)
    nid, k = base, 2
    while nid in nodes:
        nid, k = f"{base}-{k}", k + 1
    upstream = mod.startswith("WeilConjectures.")
    rel = f"lean/{pathlib.Path(*mod.split('.')).with_suffix('.lean')}"
    where = f"{'upstream' if upstream else 'SHEAF'} file {rel}{' (now in quarantine/)' if quarantined else ''}"
    w = re.search(r"\swhere\b", decl)
    cut = [k for k in (decl.find(":="), w.start() if w else -1) if k >= 0]
    sig = decl[:min(cut)].rstrip() if cut else decl
    first = re.split(r"(?<=[.])\s", " ".join(doc.split()), maxsplit=1)[0] if doc else ""
    title = (first[:150] if first else f"{short} ({kind})")
    statement = ("PROVISIONAL (machine-made from the Lean declaration; stage 1 writes it in words): "
                 + (" ".join(doc.split()) + "\n\n" if doc else "") + f"Lean ({x}):\n```lean\n{sig}\n```")
    srcdoc = (pd.get("source") or {}).get("document") if isinstance(pd.get("source"), dict) else None
    place = (f"{parent}: the Lean of this node ({how}) reaches {x}, a sorry on the sorry route of "
             f"{', '.join(sorted(info['batches']))} with no node; Lean: {where}, declaration {x} "
             f"(module {mod}, lines {a}-{b}, proof `sorry`)")
    d = {
        "id": nid,
        "blueprint": {"is": None, "from": None, "same_as": None},
        "kind": kind,
        "title": title,
        "statement": statement,
        "source": {"document": srcdoc if srcdoc and str(srcdoc).startswith("literature/") else None, "place": place},
        "stmt_deps": [],
        "proof": [],
        "proof_deps": [],
        "proof_origin": None,
        "mathlib_searches": [mathlib_grep(short)],
        "mathlib_match": None,
        "status": "unsplit",
        "merged_into": None,
        "created": {"by": "maintainer", "item": parent, "date": TODAY, "tool": "tools/route_nodes.py",
                    "why": ("PROVISIONAL: sorried declaration on the sorry route (local/sorry-route.json) with no DAG node, "
                            "recorded automatically after the route recompute (the human, 2026-10-23: every proof-related "
                            "upstream sorry gets a node, and a node without a written proof goes to stage 1). The statement "
                            "is only the Lean signature and docstring: the stage-1 worker writes it in words with [node] "
                            "citations and stmt_deps, does the Mathlib searches (LeanSearch, Loogle or LeanFinder, local grep), "
                            "fills blueprint.same_as, and splits it")},
        "chapter": pd.get("chapter"),
        "unit": pd.get("unit"),
        "lean": {"existing": True, "module": mod, "file": rel, "declaration": x, "declarations": [x],
                 "statement": decl, "by": "maintainer", "date": TODAY,
                 "note": f"{'upstream' if upstream else 'SHEAF'} declaration attached as it stands, proof still `sorry`"
                         f"{'; module quarantined (rework)' if quarantined else ''}; recorded by tools/route_nodes.py"},
    }
    if upstream:
        d["lean"]["branch"] = "slopmaster2"
        d["lean_audit"] = {"master": {"state": "none", "decls": [], "missing": [x]},
                           "slopmaster2": {"state": "sorry_here", "decls": [{"name": x, "module": mod, "lines": [a, b],
                                                                            "kind": kw, "sorry": True}],
                                           "missing": [], "open": []}}
    nodes[nid] = d
    anc, path = bp.chain(nid, nodes)
    if anc is None:   # the parent's created.item chain is broken: take the ancestor the parent records
        pf = (pd.get("blueprint") or {}).get("from") if isinstance(pd.get("blueprint"), dict) else None
        if isinstance(pf, dict) and pf.get("node"):
            anc, path = pf["node"], [nid, parent] + [v for v in (pf.get("via") or []) if v != parent]
    d["blueprint"]["from"] = {"node": anc, "via": path[1:],
                              "place": (f"provisional: the Lean of {parent} ({how}) uses {x} (route sorry with no node, "
                                        f"tools/route_nodes.py {TODAY})")}
    # 2026-10-25 (deliver3fix): a declaration whose own statement names the parent's declaration is a statement ABOUT
    # the parent (smoothPurityIso_comp_openImmersion about smoothPurityIso): citing it in the parent's proof_deps closed
    # a cycle as soon as stage 1 cited the parent in its stmt_deps. The parent gets a pointer instead (stages/1-dag.md:
    # a definition does not cite a lemma about itself) and the node goes to coord/preopen.txt.
    about = any(re.search(rf"(?<![\w']){re.escape(n.split('.')[-1])}(?![\w'])", sig) for n in node_decls(pd))
    return {"id": nid, "decl": x, "parent": parent, "how": how, "node": d, "about": about,
            "others": [c[1] for c in cs[1:6]]}, None


PRETEND = {a.split("=", 1)[1] for a in sys.argv[1:] if a.startswith("--pretend-missing=")}
OVERRIDE = dict(a.split("=", 2)[1:] for a in sys.argv[1:] if a.startswith("--parent="))


def write_json(p, d):
    p.write_text(json.dumps(d, indent=1, ensure_ascii=False) + "\n")


def main():
    write = ("--write" in sys.argv or "--commit" in sys.argv) and not PRETEND
    commit = "--commit" in sys.argv
    if not ROUTE.exists():
        print("route_nodes: no local/sorry-route.json"); return 0
    nodes = dq.load()
    miss = missing_route_decls(nodes)
    if not miss:
        print("route_nodes: every route sorry has a node"); return 0
    g = dq.Dag(nodes)
    bymod = collections.defaultdict(list)
    for i in g.live:
        m = dq.module_of(nodes[i])
        if m:
            bymod[m].append(i)
    _, imports = li.scan()
    made, errs, cache = [], [], {}
    if len(miss) > CAP:   # a broken route or record would flood the DAG: create the first CAP, say so
        print(f"route_nodes: {len(miss)} route sorries without a node, only the first {CAP} handled this pass")
    for x in sorted(miss)[:CAP]:
        r, e = build(x, miss[x], nodes, g, bymod, cache, imports)
        (made.append(r) if r else errs.append(e))
    # the parents cite the new nodes in proof_deps; check the stage-1 walk reaches them
    for r in made:
        pd = nodes[r["parent"]]
        if not r["about"]:
            pd["proof_deps"] = list(pd.get("proof_deps") or []) + [r["id"]]
    g2 = dq.Dag(nodes)
    for r in made:
        r["preopen"] = r["about"] or r["id"] not in g2.dist1
    for r in made:
        print(f"{'create' if write else 'would create'} {r['id']} ({r['node']['kind']}) for {r['decl']}; parent {r['parent']} "
              f"({r['how']}); chapter {r['node']['chapter']}/{r['node']['unit']}; from {r['node']['blueprint']['from']['node']}"
              f"{'; not reached by the stage-1 walk -> coord/preopen.txt' if r['preopen'] else ''}"
              f"{'; other candidates ' + ', '.join(r['others']) if r['others'] else ''}")
    for e in errs:
        print("route_nodes: skipped", e)
    if not write or not made:
        return 0
    lock = open(R / "coord" / ".merge.lock", "a")
    fcntl.flock(lock, fcntl.LOCK_EX)
    try:
        paths = []
        for r in made:
            d = r["node"]
            p = dq.nodes_dir() / str(d["chapter"]) / f"{d['id']}.json"
            if p.exists():
                print("route_nodes: exists, skipped", p); continue
            p.parent.mkdir(parents=True, exist_ok=True)
            write_json(p, d); paths.append(p)
            # re-read the parent under the lock (a landing may have changed it since the load)
            pp = next(dq.nodes_dir().glob(f"*/{r['parent']}.json"))
            pd = json.loads(pp.read_text())
            if r["about"] and d["id"] not in [q.get("to") for q in pd.get("pointers") or [] if isinstance(q, dict)]:
                pd["pointers"] = list(pd.get("pointers") or []) + [{"to": d["id"], "was": [], "date": TODAY,
                    "reason": "a lemma about this node's declaration (tools/route_nodes.py): a pointer, not a dependency"}]
                write_json(pp, pd)
            elif not r["about"] and d["id"] not in (pd.get("proof_deps") or []):
                pd["proof_deps"] = list(pd.get("proof_deps") or []) + [d["id"]]
                write_json(pp, pd)
            if pp not in paths:
                paths.append(pp)
        pre = [r["id"] for r in made if r["preopen"]]
        if pre:
            with PREOPEN.open("a") as f:
                f.write(f"# {TODAY} tools/route_nodes.py: route sorries with no node, not reached by the stage-1 walk\n")
                f.write("".join(f"{i}\n" for i in pre))
            paths.append(PREOPEN)
        if commit and paths:
            rel = [str(p.relative_to(R)) for p in paths]
            env = dict(os.environ, SHEAF_LEAD=os.environ.get("SHEAF_LEAD", "L-only"))
            subprocess.run(["git", "add", "--"] + rel, check=True, env=env)
            msg = (f"Route sorries without a DAG node: {len(made)} provisional maintainer stage-1 node(s) (tools/route_nodes.py)\n\n"
                   + "".join(f"- {r['id']}: {r['decl']} (parent {r['parent']}, {r['how']})\n" for r in made)
                   + "\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n")
            subprocess.run(["git", "-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", "commit", "-q",
                            "-m", msg, "--"] + rel, check=True, env=env)
            print(f"route_nodes: committed {len(rel)} file(s)")
    finally:
        fcntl.flock(lock, fcntl.LOCK_UN)
    return 0


if __name__ == "__main__":
    sys.exit(main())
