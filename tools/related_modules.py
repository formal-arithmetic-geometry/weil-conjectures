#!/usr/bin/env python3
"""The modules a change must be compiled together with before it is delivered and before it lands (decision of the owner,
2026-10-27 22:40: a delivery that changes what other modules depend on is compiled with the related modules, not with a
global build).

    tools/related_modules.py commit <sha> [--cap N] [--json]            a commit vs its first parent (graph and texts there)
    tools/related_modules.py delivery <group> <item> [--head SHA] [--json]
    tools/related_modules.py texts [--at REV] [--cap N] < {"Mod.Name": "new text" | null, ...}   (JSON on stdin; the
                                       old texts are the working tree's, or REV's; prints JSON)

Why: tonight's red builds came from (a) deliveries that changed their own module's interface and broke a direct importer,
and (b) a change of instances (the port of Derived/Monoidal, 94ef77085b4) after which an INDIRECT importer,
Sheaf.Paper.IntegralProperReductionBound, timed out in type-class search: a direct-importer check cannot see that.

The related set (name-based, read from the texts, no Lean):
  1. every direct importer of each existing module whose interface the change alters (a statement, a definition, an
     instance or attribute, a removed/added declaration, an import, variable/open/notation:
     importer_compile.interface_changed); a proof-only change has no related module;
  2. every transitive importer whose source mentions, as a whole identifier, a declaration the change added, removed or
     restated (its last name component; a component under 4 characters is matched with its namespace, `Foo.map`);
  3. when the change adds, removes or modifies an `instance`, an `attribute [instance|simp|ext|...]` (not `local`), a
     `class`/`structure`, or a declaration with such an attribute: every transitive importer that mentions one of the
     affected class/structure names (the head of each changed instance's type, e.g. `IsMonoidal`, `MonoidalCategory`,
     `Additive` for `(f)^*.Additive`; the class or structure itself; the attributed declaration).
Part 1 is never capped. Parts 2-3 are ordered nearest first (import distance), then by the number of affected class names
mentioned, and capped at --cap (SHEAF_RELATED_CAP, 150); the result says when it is capped and how many were left out.

Python: related(changes, imports, text_of, cap) with changes {module: (old text | None, new text | None)};
for_delivery(D) for a tools/stage3_delivery.read_delivery result (working-tree graph and texts).
"""
from __future__ import annotations
import collections, json, os, pathlib, re, subprocess, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import leanindex as li  # noqa: E402

ROOT = li.ROOT
CAP = int(os.environ.get("SHEAF_RELATED_CAP", "150"))
NOT_IMPORTERS = ("TargetsCheck", "Challenge")
_ATTR = re.compile(r"\b(instance|simp|ext|simps|reassoc|elementwise|norm_cast|coe|default_instance|congr|gcongr|"
                   r"mono|continuity|fun_prop|aesop|class|reducible|irreducible|semireducible|instance_reducible)\b")
# names that every module mentions: never "affected class names" (they would select everything)
_STOP = {"Type", "Sort", "Prop", "Eq", "Iff", "Ne", "Nonempty", "Fact", "True", "False", "And", "Or", "Not", "Exists",
         "Subsingleton", "Unique", "Inhabited", "Decidable", "DecidableEq", "Prefunctor", "Quiver"}


def _strip_comments(t: str) -> str:
    return re.sub(r"/-.*?-/|--[^\n]*", " ", t, flags=re.S)


def _depth0(s: str) -> str:
    """`s` with every bracketed part blanked (the closing bracket kept, so `(...).IsMonoidal` reads `).IsMonoidal`)."""
    out, d = [], 0
    for c in s:
        if c in "([{⦃⟨⟦":
            d += 1; out.append(" "); continue
        if c in ")]}⦄⟩⟧":
            d = max(0, d - 1); out.append(c if d == 0 else " "); continue
        out.append(c if d == 0 else " ")
    return "".join(out)


def conclusion(statement: str) -> str:
    """The type after the binders of a declaration's statement (its last top-level `:`), a leading `∀ ..., ` removed."""
    z = _depth0(statement)
    k = max((i for i, c in enumerate(z) if c == ":" and z[i + 1:i + 2] not in ("=",) and z[i - 1:i] != ":"), default=-1)
    c = statement[k + 1:] if k >= 0 else statement
    while True:
        m = re.match(r"\s*[∀Π]", c)
        if not m:
            break
        z = _depth0(c)
        j = z.find(",")
        if j < 0:
            break
        c = c[j + 1:]
    return c.strip()


_CHAIN = re.compile(r"(?:^|(?<=[\s)\]}⦄⟩⟧]))(\.?[^\W\d][\w'₀-₉!?]*(?:\.[^\W\d][\w'₀-₉!?]*)*)")


def classes_of(statement: str) -> set[str]:
    """The class names an instance's type is about: the head of its conclusion and every capitalized dot-suffix at the
    top level (`(f)^*⟦Λ⟧.Additive` -> Additive; `(coherentTopology Profinite).W.IsMonoidal` -> IsMonoidal)."""
    c = _depth0(conclusion(statement))
    out = set()
    for k, m in enumerate(_CHAIN.finditer(c)):
        ch = m.group(1)
        if k and not ch.startswith("."):
            continue
        seg = [x for x in ch.split(".") if x][-1:]
        if seg and seg[0][:1].isupper() and len(seg[0]) >= 3 and seg[0] not in _STOP:
            out.add(seg[0])
    return out


def _relevant(cmd: dict) -> bool:
    """an instance, class, structure, a declaration with a global attribute that changes elaboration downstream, or a
    global `attribute [...]` command"""
    if cmd["kind"] in ("instance", "class", "structure"):
        return True
    if cmd["kind"] == "other":
        t = cmd["text"]
        # `attribute [...] x in <command>` is scoped to that one command
        return (bool(re.match(r"attribute\s*\[", t)) and not re.match(r"attribute\s*\[\s*(local|scoped)\b", t)
                and not re.search(r"\sin(\s|$)", t))
    h = cmd.get("head") or ""
    return bool(re.search(r"@\[", h)) and bool(_ATTR.search(h)) and not re.search(r"@\[\s*(local|scoped)\b", h)


def _cmds(text: str | None) -> list[dict]:
    if not text:
        return []
    try:
        return li.commands(text)
    except Exception:  # noqa: BLE001   unreadable text: nothing from it (the compile tells)
        return []


_IDENT = re.compile(r"[^\W\d][\w'₀-₉!?]*(?:\.[^\W\d][\w'₀-₉!?]*)*")


_GENERIC = {"unit", "counit", "toFun", "invFun", "Functor", "Category", "CategoryTheory", "Iso", "Hom", "comp", "obj",
            "map", "inv", "app", "op", "unop", "Scheme", "Sheaf", "Type", "Module", "Ring", "CommRing", "Field"}


def constants_of(statement: str, classes: set[str]) -> set[str]:
    """the specific constants an instance's type is about (last name components of 3+ characters in its conclusion,
    without the binder variables, the classes themselves and the ubiquitous names)"""
    concl = conclusion(statement)
    binders = set()
    for grp in re.findall(r"[({\[⦃]\s*([^:(){}\[\]⦃⦄]+?)\s*:", statement[:max(0, len(statement) - len(concl))]):
        binders |= set(grp.split())
    out = set()
    for x in _IDENT.findall(concl):
        if x in binders:
            continue
        last = x.split(".")[-1]
        if len(last) >= 5 and last not in classes and last not in _STOP and last not in _GENERIC and last not in binders:
            out.add(last)
    return out


def _ident(c):
    if c["kind"] == "other":
        return ("other", c["text"])
    return (c["kind"], c["name"] or c.get("statement") or c["text"])


def relevant_keys(text: str | None) -> set:
    """(identity, head, text) of the relevant commands of a text (to recognise a command moved between modules)"""
    return {(_ident(c), c.get("head"), c["text"]) for c in _cmds(text) if _relevant(c)}


def instance_classes(old: str | None, new: str | None, moved_out: set = frozenset(),
                     moved_in: set = frozenset()) -> tuple[set[str], list[tuple[set[str], set[str]]], list[str]]:
    """(strict, added, what): the class names whose mention makes an importer related (an instance removed or
    modified, a class/structure, a global attribute, an attributed declaration); for each instance only ADDED, (its
    classes, its specific constants): an importer is related when it mentions one of the classes and, if there are such
    constants, one of them (an added `instance : IsIso (fooMap X)` matters where `fooMap` is used, not wherever `IsIso`
    is); and descriptions of the changed commands."""
    a = {_ident(c): c for c in _cmds(old) if _relevant(c)}
    b = {_ident(c): c for c in _cmds(new) if _relevant(c)}
    strict, added, what = set(), [], []
    for k in sorted(set(a) | set(b)):
        ca, cb = a.get(k), b.get(k)
        if ca and cb and (ca.get("head"), ca["text"]) == (cb.get("head"), cb["text"]):
            continue
        # moved unchanged to (from) another module of the same change: nothing changes for the importers
        if ca and not cb and (k, ca.get("head"), ca["text"]) in moved_in:
            continue
        if cb and not ca and (k, cb.get("head"), cb["text"]) in moved_out:
            continue
        c = cb or ca
        sign = "+" if ca is None else "-" if cb is None else "~"
        inst = c["kind"] == "instance" or bool(re.search(r"\binstance\b", c.get("head") or ""))
        if inst:
            got = classes_of(c.get("statement") or "")
        elif c["kind"] in ("class", "structure"):
            got = {c["name"].split(".")[-1]}
        elif c["kind"] == "other":   # attribute [..] a b c
            m = re.match(r"attribute\s*\[[^\]]*\]\s*(.*)$", c["text"])
            toks = re.split(r"\s+in\b", m.group(1))[0].split() if m else []   # `attribute [simp] foo in <decl>`
            got = {x.split(".")[-1] for x in toks if re.match(r"[^\W\d]", x)}
        else:
            got = {c["name"].split(".")[-1]} if c["name"] else set()
        got = {x for x in got if x and x not in _STOP}
        consts = set()
        if inst and sign == "+" and got:
            consts = constants_of(c.get("statement") or "", got)
            added.append((got, consts))
        else:
            strict |= got
        what.append(f"{sign}{c['kind']} {c['name'] or (c.get('statement') or c['text'])[:80]}"
                    + (f" -> {', '.join(sorted(got))}" if got else "")
                    + (f" (with {', '.join(sorted(consts)[:4])})" if consts else ""))
    return strict, added, what


def _iface(text: str | None) -> dict:
    if not text:
        return {}
    try:
        return {k: v for k, v in li.interface(text).items() if not k.startswith("#") and not k.startswith("instance ")}
    except Exception:  # noqa: BLE001
        return {}


def changed_names(old: str | None, new: str | None, moved_out: set = frozenset(), moved_in: set = frozenset()) -> set[str]:
    """qualified names a change adds (public), removes or restates (statement; a definition's text); a declaration
    moved unchanged to (from) another module of the same change is not counted"""
    a, b = _iface(old), _iface(new)
    out = {k for k in a if (k not in b and (k, a[k]) not in moved_in) or (k in b and a[k] != b[k])}
    out |= {k for k in b if k not in a and (k, b[k]) not in moved_out}
    return out


def _literal(qname: str) -> str:
    """what an importer's text must contain to mention `qname`: its last component, or the last two when that is
    shorter than 4 characters (`Foo.map`)"""
    seg = qname.split(".")
    return ".".join(seg[-2:]) if len(seg[-1]) < 4 and len(seg) > 1 else seg[-1]


def interface_changed(old: str | None, new: str | None) -> bool:
    if old is None or new is None:
        return old is not None   # a deleted module: its importers are related; a new one has none
    try:
        import stage3_delivery as s3
        d = s3.diff_module(old, new)
    except Exception:  # noqa: BLE001
        return old != new
    return bool(d.get("interface") or d.get("statement_changed") or d.get("removed") or d.get("public_imports_changed")
                or d.get("removed_imports") or d.get("added"))


def reverse(imports: dict) -> dict:
    users = collections.defaultdict(set)
    for m, imps in imports.items():
        if m in NOT_IMPORTERS:
            continue
        for i in imps:
            users[i].add(m)
    return users


def related(changes: dict, imports: dict, text_of, cap: int = CAP) -> dict:
    """changes {module: (old, new)}; imports {module: set of imported modules} (the graph the related set is read in);
    text_of(module) -> source text or None. Returns {direct: {importer: [changed modules]}, transitive: [{module, dist,
    mentions}], related: [direct ..., transitive ...], capped, left_out, candidates, names, classes, instances,
    changed: [{module, kind}]}."""
    delivered = set(changes)
    users = reverse(imports)
    direct, names, classes, added, inst, info, roots = {}, set(), set(), [], [], [], set()
    # what the change removes from one module and adds unchanged to another (a split of a module): not a change
    old_i, new_i, old_c, new_c = set(), set(), set(), set()
    for _m, (old, new) in changes.items():
        old_i |= set(_iface(old).items()); new_i |= set(_iface(new).items())
        old_c |= relevant_keys(old); new_c |= relevant_keys(new)
    for mod, (old, new) in sorted(changes.items()):
        if old is None:
            itf = new is not None
            info.append({"module": mod, "kind": "new"})
        else:
            itf = interface_changed(old, new)
            info.append({"module": mod, "kind": "interface" if itf else "proof-only"})
            if itf:
                roots.add(mod)
                for u in sorted(users.get(mod, ())):
                    if u not in delivered:
                        direct.setdefault(u, []).append(mod)
        if not itf:
            continue
        # a new module's declarations and instances reach the importers of the delivered modules that import it
        names |= changed_names(old, new, moved_out=old_i, moved_in=new_i)
        c, ad, w = instance_classes(old, new, moved_out=old_c, moved_in=new_c)
        classes |= c; added += ad; inst += [f"{mod}: {x}" for x in w]
    # distances from the changed modules over the importer graph
    dist, frontier = {m: 0 for m in roots}, list(roots)
    while frontier:
        nxt = []
        for m in frontier:
            for u in users.get(m, ()):
                if u not in dist:
                    dist[u] = dist[m] + 1; nxt.append(u)
        frontier = nxt
    lit = {}
    for n in names:
        lit.setdefault(_literal(n), set()).add(("name", n))
    for c in classes:
        lit.setdefault(c, set()).add(("class", c))
    for cl, co in added:
        for x in cl | co:
            lit.setdefault(x, set())
    cands = []
    if lit:
        alt = re.compile(r"(?<![\w'])(?:" + "|".join(re.escape(x) for x in sorted(lit, key=len, reverse=True)) + r")(?![\w'])")
        for u, d in dist.items():
            if d < 2 or u in delivered or u in direct or u in NOT_IMPORTERS:
                continue
            t = text_of(u)
            if not t:
                continue
            hit = set(alt.findall(_strip_comments(t)))
            if not hit:
                continue
            got = set()
            for h in hit:
                got |= lit.get(h, set())
            for cl, co in added:
                if hit & cl and (not co or hit & co):
                    got |= {("class", x) for x in hit & cl}
            if got:
                ncls = sum(1 for k, _ in got if k == "class")
                cands.append((d, -ncls, u, sorted({x for _, x in got})))
    cands.sort()
    keep = cands[:max(0, cap)]
    trans = [{"module": u, "dist": d, "mentions": m} for d, _n, u, m in keep]
    return {"changed": info, "direct": direct, "transitive": trans,
            "related": sorted(direct) + [x["module"] for x in trans],
            "capped": len(cands) > len(keep), "left_out": [u for _d, _n, u, _m in cands[len(keep):]],
            "candidates": len(cands), "downstream": max(0, len(dist) - len(roots)),
            "names": sorted(names), "classes": sorted(classes | {x for cl, _ in added for x in cl}),
            "instances": inst, "cap": cap}


# ---------------------------------------------------------------- graphs and texts

def _library_paths(rev: str) -> list[str]:
    roots = li.library_dirs()
    out = subprocess.run(["git", "ls-tree", "-r", "--name-only", rev, "--", *[f"lean/{r}" for r in roots],
                          "lean/Challenge.lean", "lean/TargetsCheck.lean"], cwd=ROOT, capture_output=True, text=True,
                         check=True).stdout.split()
    return [p for p in out if p.endswith(".lean") and "/.sandbox/" not in p and "/.lake/" not in p]


def texts_at(rev: str) -> dict:
    """module -> text of every library file at `rev` (git cat-file --batch)."""
    paths = _library_paths(rev)
    p = subprocess.Popen(["git", "cat-file", "--batch"], cwd=ROOT, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    import threading
    def feed():
        for x in paths:
            p.stdin.write(f"{rev}:{x}\n".encode())
        p.stdin.close()
    th = threading.Thread(target=feed); th.start()
    out = {}
    for x in paths:
        head = p.stdout.readline().split()
        if len(head) < 3 or head[1] == b"missing":
            continue
        n = int(head[2]); data = p.stdout.read(n); p.stdout.read(1)
        out[x[len("lean/"):-len(".lean")].replace("/", ".")] = data.decode(errors="ignore")
    th.join(); p.wait()
    return out


def graph_of_texts(texts: dict) -> dict:
    return {m: set(li.imports_of(t)) for m, t in texts.items()}


def working_graph():
    """(imports, text_of) of the working tree (tools/stage3_delivery.scan_imports: the shared index where there is one)."""
    import stage3_delivery as s3
    imports = s3.scan_imports()

    def text_of(m):
        try:
            return li.file_of(m).read_text(errors="ignore")
        except OSError:
            return None
    return imports, text_of


def with_new_texts(imports: dict, changes: dict) -> dict:
    g = dict(imports)
    for m, (_o, n) in changes.items():
        if n is None:
            g.pop(m, None)
        else:
            g[m] = set(li.imports_of(n))
    return g


def for_delivery(D: dict, cap: int = CAP, graph=None) -> dict:
    """The related set of a read_delivery result, in the working tree's graph."""
    imports, text_of = graph or working_graph()
    ch = {m["module"]: (m.get("old"), m.get("text")) for m in D["modules"]
          if m.get("role") in ("item", "adapted", "new", "restored", "deleted") and m.get("old") != m.get("text")}
    return related(ch, with_new_texts(imports, ch), text_of, cap)


def for_commit(sha: str, cap: int = CAP) -> dict:
    parent = subprocess.run(["git", "rev-parse", f"{sha}^"], cwd=ROOT, capture_output=True, text=True, check=True).stdout.strip()
    files = subprocess.run(["git", "diff", "--name-only", parent, sha, "--", "lean"], cwd=ROOT, capture_output=True,
                           text=True, check=True).stdout.split()
    old_texts = texts_at(parent)
    ch = {}
    for p in files:
        if not p.endswith(".lean") or "/.sandbox/" in p:
            continue
        m = p[len("lean/"):-len(".lean")].replace("/", ".")
        new = subprocess.run(["git", "show", f"{sha}:{p}"], cwd=ROOT, capture_output=True, text=True)
        ch[m] = (old_texts.get(m), new.stdout if new.returncode == 0 else None)
    imports = with_new_texts(graph_of_texts(old_texts), ch)
    return related(ch, imports, old_texts.get, cap)


def render(r: dict) -> str:
    o = []; w = o.append
    for c in r["changed"]:
        w(f"changed: {c['module']} ({c['kind']})")
    if r["instances"]:
        w("instance/attribute/class changes: " + "; ".join(r["instances"][:12]) + (" ..." if len(r["instances"]) > 12 else ""))
    w(f"names: {len(r['names'])}; affected classes: {', '.join(r['classes']) or '-'}")
    w(f"direct importers: {len(r['direct'])}")
    for u, via in sorted(r["direct"].items()):
        w(f"  {u}  (imports {', '.join(via)})")
    w(f"transitive importers that mention a changed name: {len(r['transitive'])} of {r['candidates']} "
      f"(downstream {r['downstream']})" + (f"; CAPPED at {r['cap']}, {len(r['left_out'])} left out" if r["capped"] else ""))
    for x in r["transitive"]:
        w(f"  {x['module']}  (distance {x['dist']}; mentions {', '.join(x['mentions'][:6])})")
    return "\n".join(o)


def main(argv: list[str]) -> int:
    js = "--json" in argv
    cap = int(argv[argv.index("--cap") + 1]) if "--cap" in argv else CAP
    args = [a for k, a in enumerate(argv) if not a.startswith("--") and not (k and argv[k - 1] in ("--cap", "--head", "--at"))]
    if not args:
        print(__doc__); return 2
    if args[0] == "commit" and len(args) == 2:
        r = for_commit(args[1], cap)
    elif args[0] == "delivery" and len(args) == 3:
        import stage2_delivery as s2, stage3_delivery as s3
        G = s2.Git(ROOT)
        ref = argv[argv.index("--head") + 1] if "--head" in argv else f"deliver/{args[1]}/{args[2]}"
        sha = G.run("rev-parse", ref).strip()
        base = G.run("merge-base", "sheaf-dag", sha).strip()
        r = for_delivery(s3.read_delivery(G, sha, base, args[1], args[2]), cap)
    elif args[0] == "texts":
        new = json.load(sys.stdin)
        if "--at" in argv:
            texts = texts_at(argv[argv.index("--at") + 1])
            imports, text_of = graph_of_texts(texts), texts.get
        else:
            imports, text_of = working_graph()
        ch = {m: (text_of(m), t) for m, t in new.items()}
        ch = {m: v for m, v in ch.items() if v[0] != v[1]}
        r = related(ch, with_new_texts(imports, ch), text_of, cap)
        js = True
    else:
        print(__doc__); return 2
    print(json.dumps(r, indent=1) if js else render(r))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
