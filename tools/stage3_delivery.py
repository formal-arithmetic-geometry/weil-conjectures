#!/usr/bin/env python3
"""The checks of a stage-3 delivery (stages/3-proving-and-pruning.md,
roles/worker.md §2-§3, roles/lead.md §3-§4), shared by tools/preflight_delivery.py --stage 3,
tools/review_packet.py --stage 3, tools/merge_delivery.py --stage 3 and tools/review_class.py (stage-3 items).

A stage-3 item is a MODULE of the library (queue.py: a module TargetsCheck reaches that contains `sorry`): a module
of the project's root, `Sheaf.Paper.Foo`, or of the adopted source root, `WeilConjectures.X.Y` (the roots are SHEAF_LIB
in coord/sheaf.env; one Lake package since the switch to stage 3). Its delivery is a branch deliver/<G>/<module>
(e.g. deliver/C1/Sheaf.Paper.Foo, deliver/C1/WeilConjectures.AlgebraicGeometry.Curve.FieldExtension) with ONE commit
on top of sheaf-dag containing only:
  (1) the item's module lean/<module path>.lean, its proofs written (worker.md §2.4-§2.5);
  (2) ADAPTED modules: other existing modules of the library changed because the delivery changes a statement or a
      definition that they use (stage 3 §3; landed together as one set with land_set.sh);
  (3) NEW modules lean/Sheaf/<...>.lean, each the `lean.file` of a NEW node of the delivery (stage 3 §2: "a result
      the proof needs and the DAG lacks becomes a node, under the rules of stage 1"; AGENTS.md §5: every `sorry` left
      is a named theorem with its source, a natural-language proof in its docstring, and a DAG node);
  (4) node files dag/nodes/<chapter>/<id>.json: NEW nodes (stage-1 fields plus a `lean` record), or EXISTING nodes
      changed only in STAGE3_OWNS (lean, proof, proof_deps, proof_origin) and, for a changed statement (stage 3 §3),
      in statement / stmt_deps / statement_change (node_fields.check_statement_change);
  (5) change records coord/changes/<name>.md (stage 3 §3.3) when the delivery changes what other modules see;
  (6) the report coord/reports/<G>/<module>.md (worker.md §3).

Failure letters: a commit and files, b node files, c Lean text, d change records (§3), e report, f compile and the
axiom/sorry probe.

Every module is a file of Lean's module system (`module` first; the source library's modules cannot import any other
file). An import that only a proof needs is written `import X` (seen by no other module, so it changes no interface);
`public import X` is for what the statements need.

    python3 tools/stage3_delivery.py classify <G> <module> [--branch REF]   AUTO or CODEX: <reasons> (review_class)
    python3 tools/stage3_delivery.py check <G> <module> [--branch REF]      the static checks a-e, no compile
    python3 tools/stage3_delivery.py probe <file.lean>                       the text compiled for check f
"""
from __future__ import annotations
import collections, json, pathlib, re, subprocess, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import leanindex as li  # noqa: E402
import stage2_delivery as s2  # noqa: E402
from node_fields import changed_fields_except, check_statement_change  # noqa: E402

ROOT = li.ROOT
STAGE3_OWNS = ("lean", "proof", "proof_deps", "proof_origin")
STAGE3_STATEMENT = ("statement", "stmt_deps", "statement_change")      # only with a change record (stage 3 §3)
OK_AXIOMS = ("propext", "Classical.choice", "Quot.sound")               # AGENTS.md §4-§5, GOAL.md
FORBIDDEN = re.compile(r"(?<![\w.'])(?:axiom|unsafe|implemented_by|extern|opaque|sorryAx|debug\.skipKernelTC)(?![\w'])")
SORRY = re.compile(r"(?<![\w.'])(?:sorry|admit)(?![\w'])")
NOT_IMPORTERS = ("TargetsCheck", "Challenge")   # open question for the human: do these count as importers?
REPORT_SECTIONS = (                              # roles/worker.md §3, one heading per bullet, in this order
    "What changed",
    "Proved and sorry left",
    "No longer needed",
    "Where the brief, the DAG or earlier work was wrong",
)
CHANGE_SECTIONS = ("Reason", "Old", "New", "Users", "Status")   # stage 3 §3.3
STATUS = re.compile(r"^(open|landed|closed|reverted)\b")

# The probe appended to a copy of a module for check f: every constant the file adds, its axioms beyond the three
# allowed and sorryAx (transitively), and the constants whose own term uses sorryAx (directly). Tested with
# lean-lsp lean_run_code on the pinned toolchain (v4.33.1), 2026-10-12.
PROBE = """

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
  let mut cnt : Nat := 0
  for (c, ci) in env.constants.map₂.toList do
    let used := ci.type.getUsedConstants ++ (ci.value? (allowOpaque := true)).elim #[] (·.getUsedConstants)
    if used.contains ``sorryAx then logInfo m!"SHEAF-SORRY {c}"
    if c.isInternal then continue
    cnt := cnt + 1
    for a in (← Lean.collectAxioms c) do
      unless ok.contains a do logInfo m!"SHEAF-AXIOM {c} {a}"
  logInfo m!"SHEAF-PROBED {cnt}"
"""


def module_of_path(p: str) -> str:
    return p[len("lean/"):-len(".lean")].replace("/", ".")


def path_of_module(m: str) -> str:
    return "lean/" + m.replace(".", "/") + ".lean"


PROJECT_ROOT = "Sheaf"   # the root new modules go to; the other roots of SHEAF_LIB are the adopted source library


def library_roots() -> list[str]:
    try:
        return li.library_dirs()
    except SystemExit:
        return [PROJECT_ROOT]


def is_stage3_item(item: str) -> bool:
    """Stage-3 items are modules of the library (Sheaf.X.Y, WeilConjectures.X.Y); stage 1-2 items are node ids
    (lowercase, hyphens, no dot)."""
    return "." in item and "/" not in item and item.split(".")[0] in library_roots() + [PROJECT_ROOT, "WeilConjectures"]


def is_library_file(p: str) -> bool:
    return p.endswith(".lean") and any(p.startswith(f"lean/{r}/") for r in library_roots())


# ---------------------------------------------------------------- Lean text, per declaration

def decl_table(text: str) -> dict[str, dict]:
    """key -> {kw, name, statement, body (normalized), sorry (count in signature and body), private, doc}; anonymous
    instances keyed by their statement."""
    out = {}
    for d in s2.declarations(text or ""):
        key = d["name"] or f"instance {d['statement']}"
        sig = s2.mask(text)[d["kw_pos"]:d["sig_end"]]
        head = text[d["start"]:d["kw_pos"]]
        out[key] = {"kw": d["kw"], "name": d["name"], "statement": d["statement"], "body": s2.normalize(d["body"]),
                    "sorry": len(SORRY.findall(sig)) + len(SORRY.findall(d["body"])),
                    "private": bool(re.search(r"\bprivate\b", head)), "doc": d["docstring"] or ""}
    return out


def only_sorry(body: str) -> bool:
    return bool(re.fullmatch(r":=\s*(?:by\s+)?sorry", body.strip()))


def diff_module(old: str, new: str) -> dict:
    """What one module's change is, read from the two texts."""
    a, b = decl_table(old), decl_table(new)
    oi, ni = set(s2.imports(old or "")), set(s2.imports(new or ""))
    op, np_ = set(s2.public_imports(old or "")), set(s2.public_imports(new or ""))
    r = {"added_imports": sorted(ni - oi), "removed_imports": sorted(oi - ni),
         "public_imports_changed": sorted(op ^ np_),   # what other modules see of the imports
         "interface": li.interface_changes(old or "", new or "") if old else ["(new module)"],
         "added": [k for k in b if k not in a], "removed": [k for k in a if k not in b],
         "body_changed": [k for k in b if k in a and a[k]["body"] != b[k]["body"]],
         "statement_changed": [k for k in b if k in a and a[k]["statement"] != b[k]["statement"]],
         "sorry_before": sorted(k for k in a if a[k]["sorry"]), "sorry_after": sorted(k for k in b if b[k]["sorry"]),
         "forbidden_new": sorted(set(FORBIDDEN.findall(s2.mask(new or ""))) - set(FORBIDDEN.findall(s2.mask(old or "")))),
         "disputed_new": "STATEMENT-DISPUTED" in (new or "") and "STATEMENT-DISPUTED" not in (old or ""),
         "old": a, "new": b}
    r["public_added"] = [k for k in r["added"] if not b[k]["private"]]
    # a sorry the delivery leaves: in a declaration that is new or whose body it changed
    r["new_sorry"] = [k for k in r["sorry_after"] if k in r["added"] or k in r["body_changed"]]
    return r


# ---------------------------------------------------------------- the delivery

def report_section(text: str | None, title: str) -> str:
    return s2.section_text(text, title)


_SCAN = None


def scan_imports() -> dict:
    """leanindex.scan()'s import table, read once per process (it reads the whole library: about 13 s)."""
    global _SCAN
    if _SCAN is None:
        _SCAN = li.scan()[1]
    return _SCAN


def downstream_users(changed: dict[str, list[str]]) -> dict[str, list[str]]:
    """module -> the changed names it mentions, over the modules downstream of the changed modules (as
    tools/downstream.py --uses; textual, an over-approximation the record may answer with 'not affected')."""
    imports = scan_imports()
    out = collections.defaultdict(list)
    for mod, names in changed.items():
        for u in sorted(li.downstream({mod}, imports)):
            p = li.file_of(u)
            if not p.is_file():
                continue
            t = li.strip(p.read_text(errors="ignore"))
            for n in names:
                seg = n.split(".")[-1]
                if re.search(r"(?<![\w'])" + re.escape(seg) + r"(?![\w'])", t):
                    out[u].append(n)
    return dict(out)


def importers(mod: str) -> list[str]:
    imports = scan_imports()
    return sorted(m for m, s in imports.items() if mod in s and m not in NOT_IMPORTERS)


def unit_route_modules(nodes: dict[str, dict]) -> dict[str, str]:
    """module -> node, for the nodes that realize a unit's statement or a step of its proof (dag/units/*.json
    `realized`): their modules must not be bypassed (stage 3 §2, SETUP.md three levels)."""
    out = {}
    for p in (ROOT / "dag" / "units").glob("*.json"):
        try:
            u = json.loads(p.read_text())
        except ValueError:
            continue
        r = u.get("realized") or {}
        ids = list(r.get("statement") or [])
        for s in r.get("steps") or []:
            ids += s if isinstance(s, list) else (s.get("nodes") or [] if isinstance(s, dict) else [s])
        for i in ids:
            l = (nodes.get(i) or {}).get("lean") if isinstance(i, str) else None
            if isinstance(l, dict) and str(l.get("module") or "").startswith("Sheaf."):
                out[l["module"]] = i
    return out


def target_names() -> set[str]:
    c = li.LEAN / "Challenge.lean"
    return set(re.findall(r"^theorem\s+([^\s({\[:]+)", c.read_text(), re.M)) if c.is_file() else set()


def claim_holder(mod: str) -> str | None:
    p = ROOT / "coord" / "claims" / (mod.replace("/", "__") + ".lock")
    try:
        return json.loads(p.read_text()).get("who")
    except (OSError, ValueError):
        return None


def read_delivery(git: s2.Git, ref: str, base: str, group: str, item: str, overrides: dict | None = None) -> dict:
    """The static checks a-e of the delivery `ref` against `base`. `overrides` {path: text}: a reviewer's fixed files
    (merge_delivery.py --stage 3 --apply-fixes). Returns {fails, notes, base, commits, modules: [{file, module, role
    (item|adapted|new), old, text, diff}], nodes: {id: {path, node, base_node, role (new|changed)}}, changes: {path:
    text}, report, report_path, interface (module -> changed names), users, roles}."""
    D = {"fails": [], "notes": [], "modules": [], "nodes": {}, "changes": {}, "report": None, "commits": [],
         "report_path": f"coord/reports/{group}/{item}.md", "interface": {}, "users": {}, "roles": []}
    over = overrides or {}
    f = lambda L, s: D["fails"].append((L, s))  # noqa: E731
    show = lambda p: over[p] if p in over else git.show(ref, p)  # noqa: E731
    if not is_stage3_item(item):
        f("a", f"{item} is not a module of the library ({', '.join(r + '.<...>' for r in library_roots())}; a stage-3 item "
               "is a module)"); return D
    if not git.ok("rev-parse", "--verify", "-q", ref) or not git.ok("rev-parse", "--verify", "-q", base):
        f("a", f"no ref {ref} or {base}"); return D
    mb = git.run("merge-base", base, ref).strip()
    if mb != git.run("rev-parse", base).strip():
        D["notes"].append(f"{ref} is based on {mb[:9]} (sheaf-dag has moved on); checked against that base")
    base = D["base"] = mb
    D["commits"] = git.run("rev-list", "--reverse", f"{base}..{ref}").split()
    if len(D["commits"]) != 1:
        f("a", f"{len(D['commits'])} commits beyond {base[:9]}: deliver one module as exactly one commit")
    item_file = path_of_module(item)
    status = [l.split("\t") for l in git.run("diff", "--name-status", base, ref).splitlines() if l]
    seen_item = False
    for st in status:
        code, p = st[0], st[-1]
        if code[0] in "DR":
            f("a", f"{p}: the delivery deletes or renames a file (a module that leaves the reach is pruned by the "
                   "maintainer's queue, never deleted by a delivery)"); continue
        if p == D["report_path"]:
            continue
        if is_library_file(p):
            old = git.show(base, p) if code[0] != "A" else None
            role = "item" if p == item_file else ("new" if old is None else "adapted")
            if role == "new" and not p.startswith(f"lean/{PROJECT_ROOT}/"):
                f("a", f"{p}: a new module goes under lean/{PROJECT_ROOT}/ (the project's root; the source root only "
                       "holds the modules adopted from the source repository)")
            seen_item |= role == "item"
            D["modules"].append({"file": p, "module": module_of_path(p), "role": role, "old": old, "text": show(p)})
        elif p.startswith("dag/nodes/") and p.endswith(".json"):
            nid = pathlib.PurePosixPath(p).stem
            try:
                node = json.loads(show(p) or "")
                bn = json.loads(git.show(base, p)) if code[0] != "A" else None
            except ValueError:
                f("b", f"{p} is not valid JSON"); continue
            D["nodes"][nid] = {"path": p, "node": node, "base_node": bn, "role": "new" if bn is None else "changed"}
        elif p.startswith("coord/changes/") and p.endswith(".md"):
            D["changes"][p] = show(p)
        else:
            f("a", f"{p}: not a file a stage-3 delivery may change (a module of the library under "
                   f"{', '.join('lean/' + r + '/' for r in library_roots())}; dag/nodes/; coord/changes/; {D['report_path']})")
    if not seen_item:
        f("a", f"the item's module {item_file} is not changed by the delivery")
    for m in D["modules"]:
        m["diff"] = diff_module(m["old"], m["text"])
        D["roles"].append(f"{m['role']} module {m['file']}")
    D["report"] = show(D["report_path"])
    nodes_base = s2.nodes_at(git, base)
    dmap = s2.declaration_map({**nodes_base, **{k: v["node"] for k, v in D["nodes"].items()}})
    check_lean(D, f, dmap)
    check_nodes(D, f, git, base, group, item, nodes_base)
    check_changes(D, f, group, nodes_base)
    check_report(D, f, group)
    return D


def check_lean(D, f, dmap):
    for m in D["modules"]:
        text, d, where = m["text"] or "", m["diff"], m["file"]
        if not s2.is_module(text):
            f("c", f"{where}: not a file of Lean's module system (the first command is `module`; a new module is written "
                   "like the library's: `module`, `public import ...`, `@[expose] public section`; tools/to_module.py "
                   "converts a file)")
        for imp in d["added_imports"]:
            if not imp.startswith(s2.IMPORT_OK):
                f("c", f"{where}: import {imp}: only Mathlib.*, WeilConjectures.*, Sheaf.*")
        for k, line in enumerate(text.split("\n"), 1):
            if len(line) > 100:
                f("c", f"{where}: line {k} has {len(line)} characters (at most 100)")
        if d["forbidden_new"]:
            f("c", f"{where}: new {', '.join(d['forbidden_new'])}: no axiom, no unsafe/extern/implemented_by/opaque "
                   "escape (AGENTS.md §4: no axiom beyond propext, Classical.choice, Quot.sound)")
        for k in d["new_sorry"]:
            x = d["new"][k]
            if x["kw"] not in s2.THEOREM_KW:
                f("c", f"{where}: {k}: `sorry` in a {x['kw']} (a hollow definition, AGENTS.md §5)")
            elif x["private"] or not x["name"]:
                f("c", f"{where}: {k}: a `sorry` left in a private or anonymous declaration; a sorry left is a named "
                       "theorem with its node (AGENTS.md §5)")
            elif not only_sorry(x["body"]):
                f("c", f"{where}: {k}: a partial proof with `sorry` inside; split the gap into a named theorem with "
                       "its source, a natural-language proof in its docstring and a DAG node (AGENTS.md §5)")
            elif x["name"] not in dmap:
                f("c", f"{where}: {k} is left with `sorry` and no node records it (lean.declaration(s) of a node of "
                       "the base or of the delivery; AGENTS.md §5)")
            elif f"(blueprint: {dmap[x['name']]})" not in x["doc"]:
                f("c", f"{where}: the docstring of {k} lacks `(blueprint: {dmap[x['name']]})` and the proof in words")
        if d["interface"] and m["role"] != "new":
            D["interface"][m["module"]] = [x for x in d["interface"] if not x.startswith("(")] or d["interface"]
    tn = target_names()
    for m in D["modules"]:
        if m["role"] == "new":
            continue
        d = m["diff"]
        hit = sorted((set(d["statement_changed"]) | set(d["removed"]) | set(D["interface"].get(m["module"], []))) & tn)
        mod = m["module"]
        if hit:
            f("c", f"{mod}: changes the target statement(s) {', '.join(hit)} (lead.md §3: no target statement changes;"
                   " AGENTS.md §4: only on the human's instruction)")


def check_nodes(D, f, git, base, group, item, nodes_base):
    delivered_files = {m["file"] for m in D["modules"]}
    for nid, x in D["nodes"].items():
        d, b, p = x["node"], x["base_node"], x["path"]
        if x["role"] == "changed":
            bad = changed_fields_except(b, d, owns=STAGE3_OWNS + STAGE3_STATEMENT)
            if bad:
                f("b", f"{p}: changes {', '.join(bad)} (a stage-3 delivery sets only {', '.join(STAGE3_OWNS)}, and "
                       f"{', '.join(STAGE3_STATEMENT)} with a change record)")
            if any(b.get(k) != d.get(k) for k in STAGE3_STATEMENT):
                citers = sorted(i for i, n in nodes_base.items()
                                if nid in (n.get("stmt_deps") or []) or nid in (n.get("proof_deps") or []))
                for e in check_statement_change(b, d, citers):
                    f("b", f"{p}: {e}")
                D["notes"].append(f"{nid}: statement changed ({len(citers)} citers): a change record is required")
            continue
        # a new node: stage-1 fields (stages/1-dag.md §3-§6) plus the `lean` record of its module
        for k in ("id", "kind", "title", "statement", "source", "stmt_deps", "proof", "proof_deps", "proof_origin",
                  "mathlib_searches", "status", "created", "blueprint", "chapter", "unit", "lean"):
            if k not in d:
                f("b", f"{p}: new node without `{k}`")
        if d.get("id") != nid:
            f("b", f"{p}: id {d.get('id')!r} is not the file name")
        if nid in nodes_base:
            f("b", f"{p}: {nid} exists on sheaf-dag")
        c = d.get("created") or {}
        if c.get("item") != item or c.get("group") != group:
            f("b", f"{p}: created must be {{by: worker, item: {item}, date, group: {group}}}")
        kinds = {s2.search_kind(s.get("tool")) for s in d.get("mathlib_searches") or [] if isinstance(s, dict)}
        if not {"leansearch", "loogle/leanfinder", "grep"} <= kinds:
            f("b", f"{p}: three kinds of Mathlib search are required (stage 1 rules)")
        uses = set()
        for s in d.get("proof") or []:
            if not isinstance(s, dict) or "text" not in s or not isinstance(s.get("elementary"), bool):
                f("b", f"{p}: a proof step is not {{text, uses, elementary}}"); continue
            uses |= set(s.get("uses") or [])
        if d.get("kind") != "definition" and not d.get("proof"):
            f("b", f"{p}: a new statement node carries its proof in steps (stage 1 rules; AGENTS.md §5)")
        if set(d.get("proof_deps") or []) != uses:
            f("b", f"{p}: proof_deps is not the union of the steps' uses")
        if (d.get("blueprint") or {}).get("is") is not None:
            f("b", f"{p}: blueprint.is must be null on a new node")
        lf = (d.get("lean") or {}).get("file")
        for e in s2.check_record(d.get("lean"), group, f"{nid}.lean"):
            # a new node may be stated in a module of the delivery that is not under Sheaf (the item's own module)
            if "is not Sheaf.<Topic>.<Name>" in e[1] and lf in delivered_files:
                continue
            f(*e)
        mod = next((m for m in D["modules"] if m["file"] == lf), None)
        decl = (d.get("lean") or {}).get("declaration")
        if mod is not None and decl not in mod["diff"]["new"]:
            f("b", f"{p}: lean.declaration {decl!r} is not declared in {lf}")
        elif mod is not None and s2.normalize((d.get("lean") or {}).get("statement")) != mod["diff"]["new"][decl]["statement"]:
            f("b", f"{p}: lean.statement differs from the signature of {decl} in {lf}")
        if lf and lf not in delivered_files and git.show(base, lf) is None:
            f("b", f"{p}: lean.file {lf} is neither delivered nor on sheaf-dag")
    for m in D["modules"]:
        if m["role"] == "new" and not any((x["node"].get("lean") or {}).get("file") == m["file"] for x in D["nodes"].values()):
            f("b", f"{m['file']}: a new module is the lean.file of a new node of the delivery")


def check_changes(D, f, group, nodes_base):
    stmt_changed = [n for n, x in D["nodes"].items() if x["role"] == "changed" and
                    any((x["base_node"] or {}).get(k) != x["node"].get(k) for k in STAGE3_STATEMENT)]
    if (D["interface"] or stmt_changed) and not D["changes"]:
        f("d", "the delivery changes what other modules see (" + "; ".join(
            f"{m}: {', '.join(v[:4])}" for m, v in D["interface"].items()) + (f"; node statements {stmt_changed}"
            if stmt_changed else "") + "): write coord/changes/<name>.md (stage 3 §3.3)")
    D["users"] = downstream_users(D["interface"]) if D["interface"] else {}
    alltext = "\n".join(t or "" for t in D["changes"].values())
    for p, t in D["changes"].items():
        for s in CHANGE_SECTIONS:
            if not report_section(t, s):
                f("d", f"{p}: section `## {s}` missing or empty (stage 3 §3.3: reason, old and new version, effect on "
                       "each user, status)")
        st = report_section(t, "Status")
        if st and not STATUS.match(st):
            f("d", f"{p}: `## Status` starts with open, landed, closed or reverted")
        elif st and not st.startswith("open"):
            f("d", f"{p}: a delivered change record has status `open` (the merge writes `landed`, the lead `closed`)")
    for u, names in D["users"].items():
        if f"`{u}`" not in alltext and f"| {u} " not in alltext:
            f("d", f"user {u} (mentions {', '.join(names[:3])}) is not in a change record's `## Users`")
    for m in D["modules"]:
        if m["role"] == "adapted":
            who = claim_holder(m["module"])
            if who not in (group, None) and who not in alltext:
                f("d", f"{m['module']} is claimed by {who}: change only what the adaptation needs and name it and its"
                       " group in the record (stage 3 §3.1)")
            elif who is None:
                f("d", f"{m['module']} is adapted but nobody claims it: claim it first (lead.md §2.1)")


def check_report(D, f, group):
    t = D["report"]
    if not t:
        f("e", f"no report {D['report_path']}"); return
    for s in REPORT_SECTIONS + (f"Second reading by {group}",):
        if not report_section(t, s):
            f("e", f"report: section `## {s}` missing or empty (roles/worker.md §3)")
    left = report_section(t, "Proved and sorry left")
    for m in D["modules"]:
        # the item module: every sorry it still has; an adapted or new module: the sorries the delivery leaves
        for k in (m["diff"]["sorry_after"] if m["role"] == "item" else m["diff"]["new_sorry"]):
            if k.split(".")[-1] not in left:
                f("e", f"report: {k} in {m['module']} still has `sorry` and is not named under `## Proved and sorry "
                       "left` (worker.md §3: every sorry left, by name)")
    new_ids = [n for n, x in D["nodes"].items() if x["role"] == "new"]
    if new_ids:
        sec = report_section(t, "New nodes")
        for n in new_ids:
            if n not in sec:
                f("e", f"report: `## New nodes` does not name {n}")
    for p in D["changes"]:
        if p not in t:
            f("e", f"report: does not name the change record {p}")


# ---------------------------------------------------------------- check f: compile with the probe

def probe(D: dict, group: str, root: pathlib.Path | None = None, timeout: int = 120) -> list[dict]:
    """Compile each module with PROBE appended (s2.compile_text), in import order, deferring a module that imports a
    delivered sibling not yet in the library. Returns [{file, status, out, axioms: [(decl, axiom)], sorry: [owner]}]."""
    root = root or s2.compile_root()
    mods = {m["module"]: m for m in D["modules"]}
    res = []
    for m in D["modules"]:
        sib = [i for i in s2.imports(m["text"] or "") if i in mods and i != m["module"]]
        if any(not s2.landed_same(root, s, mods[s]["text"] or "") for s in sib):
            res.append({"file": m["file"], "status": "deferred", "out": "imports a delivered sibling", "axioms": [], "sorry": []}); continue
        ran, rc, out = s2.compile_text((m["text"] or "") + PROBE, group, m["module"].replace(".", "_") + "__probe", root, timeout)
        ax = re.findall(r"SHEAF-AXIOM (\S+) (\S+)", out)
        so = sorted({owner(x, m["diff"]["new"]) for x in re.findall(r"SHEAF-SORRY (\S+)", out)})
        st = "not run" if not ran else ("ok" if rc == 0 and "SHEAF-PROBED" in out else "fail")
        res.append({"file": m["file"], "status": st, "out": out, "axioms": ax, "sorry": so})
    return res


def owner(c: str, table: dict) -> str:
    """The declaration of the file an auxiliary constant belongs to (`foo._proof_1`, `_private.….0.foo`)."""
    if ".0." in c and c.startswith("_private."):
        c = c.split(".0.", 1)[1]
    parts = c.split(".")
    for k in range(len(parts), 0, -1):
        cand = ".".join(parts[:k])
        if cand in table:
            return cand
    return c


def probe_fails(D: dict, results: list[dict]) -> list[tuple[str, str]]:
    out = []
    for r, m in zip(results, D["modules"]):
        if r["status"] == "fail":
            out.append(("f", f"{r['file']} does not compile with the probe:\n   " + "\n   ".join(r["out"].splitlines()[-30:])))
        for decl, a in r["axioms"]:
            out.append(("f", f"{r['file']}: {decl} uses the axiom {a} (AGENTS.md §4: only {', '.join(OK_AXIOMS)})"))
        allowed = set(m["diff"]["sorry_before"]) - set(m["diff"]["body_changed"]) | set(m["diff"]["new_sorry"])
        extra = [s for s in r["sorry"] if s not in allowed]
        if extra:
            out.append(("f", f"{r['file']}: Lean finds `sorry` in {', '.join(extra)}, which the text check did not "
                             "(a macro or an elaborator inserted it)"))
    return out


# ---------------------------------------------------------------- tiered review (decision of the human): stage 3 has
# no Claude reviewer. AUTO: the delivery changes only proofs, compiles, leaves no new sorry without its node, adds no
# axiom and leaves the statements of existing declarations unchanged; a script lands it after the tools' own checks.
# CODEX: it changes a statement, a definition, an import other modules see, or adds nodes; an independent Codex
# reviewer on another machine reads it, and a script executes the verdict (merge_delivery.py ... --stage 3 or return).

def classify(D: dict, group: str, item: str) -> list[str]:
    """The reasons for a reader (CODEX; empty: AUTO) from the static reading; the compile and the probe are the
    merge's AUTO gate."""
    why = []
    if D["fails"]:
        why.append(f"the static checks fail ({D['fails'][0][0]}: {D['fails'][0][1][:80]})")
    if any(x["role"] == "new" for x in D["nodes"].values()):
        why.append("adds nodes")
    if any(x["role"] == "changed" for x in D["nodes"].values()):
        why.append("changes a node file")
    if D["changes"]:
        why.append("a change record (stage 3 §3)")
    others = [m["file"] for m in D["modules"] if m["role"] != "item"]
    if others:
        why.append(f"modules besides the item ({len(others)})")
    routes = None
    for m in D["modules"]:
        d = m["diff"]
        if d["interface"]:
            why.append(f"changes what other modules see in {m['module']}: {', '.join(d['interface'][:3])}")
        if d["statement_changed"]:
            why.append(f"statement changed: {', '.join(d['statement_changed'][:3])}")
        if d["public_added"]:
            why.append(f"adds public declarations {', '.join(d['public_added'][:3])} (a result the proof needs may "
                       "need a node: stage 3 §2)")
        if d["removed"]:
            why.append(f"removes declarations {', '.join(d['removed'][:3])}")
        if d["public_imports_changed"] and m["role"] == "item":
            imp = importers(m["module"])
            if imp:
                why.append(f"changes a public import ({', '.join(d['public_imports_changed'][:3])}) in a module with "
                           f"{len(imp)} importer(s): an import other modules see (an import only the proof needs is "
                           "written `import X`, without `public`)")
        if d["removed_imports"]:
            if routes is None:
                routes = unit_route_modules(s2.nodes_at(s2.Git(ROOT), D["base"]))
            hit = [i for i in d["removed_imports"] if i in routes]
            if hit:
                why.append(f"removes the import of unit-route module(s) {', '.join(hit)} (stage 3 §2: no unit bypassed)")
        if d["new_sorry"]:
            why.append(f"leaves sorry in {', '.join(d['new_sorry'][:3])}")
        if d["forbidden_new"]:
            why.append(f"new {', '.join(d['forbidden_new'])}")
        if d["disputed_new"]:
            why.append("STATEMENT-DISPUTED")
    rep = D.get("report") or ""
    if any(not re.match(r"\s*`?\s*(none|no\b|n/a|nothing)", x, re.I) for x in re.findall(r"STATEMENT-DISPUTED:(.{0,40})", rep)):
        why.append("STATEMENT-DISPUTED in the report")
    ret = ROOT / "coord" / "returns" / f"{group}.md"
    if ret.exists() and f"## {item} (" in ret.read_text():
        why.append("repair of a returned delivery")
    return list(dict.fromkeys(why))


def main(argv: list[str]) -> int:
    if argv and argv[0] == "probe" and len(argv) == 2:
        print(pathlib.Path(argv[1]).read_text() + PROBE); return 0
    if len(argv) >= 3 and argv[0] in ("classify", "check"):
        g, item = argv[1], argv[2]
        ref = argv[argv.index("--branch") + 1] if "--branch" in argv else f"deliver/{g}/{item}"
        D = read_delivery(s2.Git(ROOT), ref, "sheaf-dag", g, item)
        if argv[0] == "classify":
            why = classify(D, g, item)
            print("AUTO" if not why else "CODEX: " + "; ".join(why)); return 0
        for r in D["roles"]:
            print("  " + r)
        for n in D["notes"]:
            print(" ! " + n)
        for L, x in D["fails"]:
            print(f" ({L}) {x}")
        print("static checks OK (stage 3)" if not D["fails"] else f"{len(D['fails'])} failure(s)")
        return 1 if D["fails"] else 0
    print(__doc__); return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
