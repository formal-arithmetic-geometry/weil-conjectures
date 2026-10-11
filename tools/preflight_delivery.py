#!/usr/bin/env python3
"""Preflight of a stage-1 delivery, run by a remote group on its own clone before every push.

    python3 tools/preflight_delivery.py <group> <item> [--base origin/sheaf-dag]

Needs no server access: it compares HEAD with the base (default origin/sheaf-dag; run
`git fetch origin` first so that the base is the current tip) and prints every reason for
which the maintainer would return the delivery without reading it. Exit code 0 means
"nothing found by the script" (the mathematics is still reviewed by the maintainer); a
non-zero exit code comes with the list of failures, and a delivery that fails is not pushed.

Checks (roles/remote-lead.md §4-5, the returns of 2026-10-09):
  1. the working tree is clean and HEAD is exactly one commit on top of the base;
  2. only the item's node, its new nodes (created.item = item), the realized fields of the
     item's unit record and coord/reports/<group>/<item>.md changed; no claim lock, no queue;
  3. the report exists and has a non-empty "## Review by <group>" section that is not a copy of
     the worker's sections and does not say the review is pending;
  4. every new node: created.item = item, a name that does not exist on the base, a statement
     that cites nodes, no proof sketch in the statement, status unsplit (no proof steps) or
     mathlib (a match with declaration, file and line), three kinds of Mathlib search;
  5. the item: status split (or a Mathlib leaf), split_report, proof_origin, every step with
     text and a boolean elementary, cited nodes or elementary, proof_deps = union of uses;
  6. a Stacks tag (0XYZ) or section number (a.b.c) written in a statement or a step is carried
     by a cited node (or by the node itself); a non-elementary step that only quotes a tag fails;
     a step marked elementary may name a tag for a fact of two or three lines (warning only;
     the reviewer judges whether it is elementary; rule of 2026-10-10 17:10 UTC);
  7. tools/review_split.py <item> passes and tools/check_dag.py reports no cycle, route or
     dependency error;
  8. blueprint references (stages/1-dag.md §6, rule of 2026-10-10): the item and every new node
     carry the `blueprint` field; `from.place` is filled (not "unspecified"); `same_as` is a list
     (the whole blueprint was searched with tools/blueprint_refs.py search); a new node's
     `from.node` is the item's nearest blueprint ancestor; the item's split_report has a
     `blueprint` entry naming the places of the blueprint proof the steps realize;
  9. fields (decision of the human, 2026-10-10, evening; tools/node_fields.py, tools/README.md "Fields of a
     node"): the item's node is taken as it is on the base and only the fields a split owns are set; every
     maintainer's field (lean_audit, lean, blueprint.is, created, reviewed, lead_note, tool_uses, import_flags,
     ...) must be unchanged against the base, and a new node has blueprint.is null and no maintainer's fields
     except created.

Stage 2 (stages/2-statements.md; the format is in tools/stage2_delivery.py and tools/README.md "Stage 2"):

    python3 tools/preflight_delivery.py <group> <item> --stage 2 [--base origin/sheaf-dag] [--branch <ref>]

checks the branch <ref> (default HEAD; the lead passes deliver/<group>/<item>) against the base:
  a. one commit on top of the base with only modules lean/Sheaf/**/*.lean, node files and the report;
  b. the item changed only in `lean` (and in `stmt_deps` by adding new nodes of the delivery), a record {module,
     declaration, [declarations], [file], statement, branch, by, date, existing} with the module matching the file and
     by = <group>; each other node file classified (printed) as a NEW definition node (absent on the base; the field
     rule of tools/stage2_delivery.py check_new_node, coord/STATE.md "STAGE 2 EXTRA NODES") or a DEPENDENCY node (in
     the item's stmt_deps on the base, changed only in `lean`, existing false, with lean.note); every module the
     lean.file of exactly one node, every node with existing false with its module; a CORRECTED item (STAGE 2
     STATEMENT CORRECTION: statement changed, and as far as forced stmt_deps, proof, proof_deps) with its
     statement_change checked by tools/node_fields.py check_statement_change (citers = the base nodes citing the item),
     printed as "item corrected: <n> citers, <k> marked holds:false";
  c. each module, with its own node's id: imports of Mathlib.*, WeilConjectures.*, Sheaf.* only; lines of at most 100
     characters; the declaration defined, its docstring with `(blueprint: <node id>)`, its name not already in Mathlib or the source;
     every theorem/lemma proved by `sorry`, no `sorry` in a definition; the recorded statement equal to the file's;
  d. an existing declaration (existing: true): no Lean file, module Mathlib.* or WeilConjectures.*, declared there;
  e. the report with non-empty `## Worker report` and `## Second reading by <group>`, and `## New nodes` /
     `## Dependency modules` naming each new node / dependency node when there are any, and `## Statement corrected`
     naming each citer when the item is corrected;
  f. the compile of each module with tools/lean_file.sh in lean/.sandbox/<group>/<node>.lean, in dependency order;
     a module importing a sibling module not yet in the library prints "compile: deferred"; on the server only
     (SHEAF_COMPILE_ROOT names another project directory to compile in).
Prints "preflight OK (stage 2)" or every failure with its letter, exit code 1.
"""
from __future__ import annotations
import json, pathlib, re, subprocess, sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from node_fields import MAINTAINER, changed_maintainer_fields  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
TAG = re.compile(r"(?<![A-Za-z0-9])0[0-9A-Z]{3}(?![A-Za-z0-9])")
SECTION = re.compile(r"(?<![\d.])\d{1,2}\.\d{1,3}\.\d{1,3}(?![\d.])")
CITE = re.compile(r"\[([a-z][a-z0-9]*(?:-[a-z][a-z0-9]*)+)\]")   # a node id: hyphen-separated segments each starting with a letter; [n-1] is not a citation


def git(*args: str, check: bool = True) -> str:
    r = subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)
    if check and r.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)}: {r.stderr.strip()}")
    return r.stdout.rstrip("\n")


def exists_at(ref: str, path: str) -> bool:
    return subprocess.run(["git", "cat-file", "-e", f"{ref}:{path}"], cwd=ROOT, capture_output=True).returncode == 0


def load_at(ref: str, path: str) -> dict:
    return json.loads(git("show", f"{ref}:{path}"))


def node_ids_at(ref: str) -> dict[str, str]:
    out = git("ls-tree", "-r", "--name-only", ref, "--", "dag/nodes")
    ids = {}
    for p in out.splitlines():
        if p.endswith(".json"):
            ids[pathlib.PurePosixPath(p).stem] = p
    return ids


def carried(token: str, d: dict) -> bool:
    return token in json.dumps(d, ensure_ascii=False)


def text_tokens(s: str) -> tuple[set[str], set[str]]:
    return set(TAG.findall(s or "")), set(SECTION.findall(s or ""))


def default_base() -> str:
    """origin/sheaf-dag on a remote clone; sheaf-dag on the server, where the branch is local (lead, 2026-10-11)."""
    import subprocess
    r = subprocess.run(["git", "rev-parse", "--verify", "-q", "origin/sheaf-dag"], capture_output=True, text=True)
    return "origin/sheaf-dag" if r.returncode == 0 else "sheaf-dag"


def main_stage2(argv: list[str]) -> int:
    import stage2_delivery as s2
    base, branch, args = default_base(), None, []
    i = 0
    while i < len(argv):
        a = argv[i]
        if a in ("--base", "--branch", "--stage") and i + 1 < len(argv):
            if a == "--base":
                base = argv[i + 1]
            elif a == "--branch":
                branch = argv[i + 1]
            i += 2; continue
        if a.startswith("--base="):
            base = a.split("=", 1)[1]
        elif a.startswith("--branch="):
            branch = a.split("=", 1)[1]
        elif not a.startswith("--stage"):
            args.append(a)
        i += 1
    if len(args) != 2:
        print(__doc__); return 2
    group, item = args
    g = s2.Git(ROOT)
    ref = branch or "HEAD"
    D = s2.read_delivery(g, ref, base, group, item)
    fails = list(D["fails"])
    if branch is None:
        dirty = g.run("status", "--porcelain")
        if dirty:
            fails.insert(0, ("a", "uncommitted changes in the working tree (commit them into the one delivery commit, or stash):\n   "
                             + "\n   ".join(dirty.splitlines()[:10])))
    print(f"delivery of {item} by {group}: the item ({D['node_path']})")
    for r in D.get("roles") or []:
        print(f"   {r}")
    if D.get("corrected"):
        nf = sum(1 for c in D.get("citer_marks") or [] if c.get("holds") is False)
        print(f"item corrected: {len(D.get('citers') or [])} citers, {nf} marked holds:false")
    compiled = []
    for c in s2.compile_modules(D, group):
        where = f"{c['file']} ({c['node']})"
        if c["status"] == "fail":
            fails.append(("f", f"{where} does not compile (exit {c['rc']}):\n   " + "\n   ".join(c["out"].splitlines()[-40:])))
        elif c["status"] == "ok":
            compiled.append(f"{where}: compile: OK\n   " + "\n   ".join(c["out"].splitlines()[-15:]))
        else:
            compiled.append(f"{where}: {c['out']}")
    for n in D["notes"]:
        print(f" ! {n}")
    for c in compiled:
        print(c)
    if not fails:
        print("preflight OK (stage 2)")
        return 0
    order = "abcdef"
    fails.sort(key=lambda x: order.index(x[0]))
    print(f"preflight FAILED (stage 2), {len(fails)} reason(s); do not push:")
    for L, x in fails:
        print(f" ({L}) {x}")
    return 1


def main() -> int:
    if "--stage" in sys.argv[1:] or any(a.startswith("--stage=") for a in sys.argv[1:]):
        argv = sys.argv[1:]
        st = next((a.split("=", 1)[1] for a in argv if a.startswith("--stage=")), None)
        if st is None:
            k = argv.index("--stage")
            st = argv[k + 1] if k + 1 < len(argv) else ""
        if st == "2":
            return main_stage2(argv)
        if st != "1":
            print(f"--stage {st!r}: 1 or 2"); return 2
        sys.argv = [sys.argv[0]] + [a for k, a in enumerate(argv) if not (a.startswith("--stage") or (k > 0 and argv[k - 1] == "--stage"))]
    args: list[str] = []
    base = default_base()
    argv = sys.argv[1:]
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--base" and i + 1 < len(argv):
            base = argv[i + 1]; i += 2; continue
        if a.startswith("--base="):
            base = a.split("=", 1)[1]; i += 1; continue
        args.append(a); i += 1
    if len(args) != 2:
        print(__doc__); return 2
    group, item = args
    fails: list[str] = []
    warns: list[str] = []
    f = fails.append

    # 1. clean tree, one commit on top of the base
    try:
        git("rev-parse", "--verify", "-q", base)
    except RuntimeError:
        print(f"no ref {base}: run `git fetch origin` (or pass --base <ref>)"); return 2
    dirty = git("status", "--porcelain")
    if dirty:
        f("uncommitted changes in the working tree (commit them into the one delivery commit, or stash):\n   " + "\n   ".join(dirty.splitlines()[:10]))
    commits = git("rev-list", "--reverse", f"{base}..HEAD").split()
    if not commits:
        f(f"HEAD has no commit beyond {base} (the branch would deliver nothing)")
    elif len(commits) != 1:
        f(f"{len(commits)} commits beyond {base}: deliver one item as exactly one commit (squash with `git reset --soft {base}` and commit again)")
    if git("merge-base", "--is-ancestor", base, "HEAD", check=False) == "" and subprocess.run(["git", "merge-base", "--is-ancestor", base, "HEAD"], cwd=ROOT).returncode != 0:
        f(f"HEAD is not on top of {base}: fetch, rebase onto {base}, and run again")

    # 2. the files
    head_ids = node_ids_at("HEAD")
    base_ids = node_ids_at(base)
    item_path = head_ids.get(item)
    if item_path is None:
        f(f"no node file for the item {item} at HEAD"); print_result(fails, warns); return 1
    if item not in base_ids:
        f(f"the item {item} does not exist on {base} (a delivery splits an existing node)")
    unit = load_at("HEAD", item_path).get("unit")
    report = f"coord/reports/{group}/{item}.md"
    files = git("diff", "--name-only", base, "HEAD").splitlines() if commits else []
    new_paths: list[str] = []
    for p in files:
        if p == item_path or p == report:
            continue
        if p.startswith("dag/nodes/") and p.endswith(".json"):
            if exists_at(base, p):
                f(f"{p}: a node that already exists on {base} was modified; only the item's node may change")
            else:
                new_paths.append(p)
        elif unit and p == f"dag/units/{unit}.json":
            a, b = load_at(base, p), load_at("HEAD", p)
            for k in ("realized", "realized_by"):
                a.pop(k, None); b.pop(k, None)
            if a != b:
                f(f"{p}: only the realized fields of the unit record may change")
        elif p.startswith("coord/claims/"):
            f(f"{p}: a claim lock file is in the delivery; claims are made with tools/claim.py on the server, never pushed")
        else:
            f(f"{p}: file outside the item's files (allowed: the item's node, its new nodes, dag/units/{unit}.json realized fields, {report})")
    if commits and item_path not in files:
        f("the item's node file is unchanged")

    # 3. the report
    if not exists_at("HEAD", report):
        f(f"no report file {report}")
        review = ""
    else:
        text = git("show", f"HEAD:{report}")
        sections = re.split(r"(?m)^## ", text)
        review = ""
        others = []
        for s in sections[1:]:
            if s.startswith(f"Review by {group}"):
                review = s[len(f"Review by {group}"):].strip()
            else:
                others.append(s)
        if not review:
            f(f"the report has no non-empty section '## Review by {group}' (the group's own review of the mathematics)")
        else:
            if len(review.split()) < 40:
                f("the review section is too short to be a review (fewer than 40 words)")
            if re.search(r"\b(pending|to be reviewed|not yet reviewed)\b", review, re.I):
                f("the review section says the review is pending; a delivery is reviewed before it is pushed")
            rest = "\n".join(others)
            copied = [s.strip() for s in re.split(r"(?<=[.!?])\s+", review) if len(s.strip()) >= 60 and s.strip() in rest]
            if copied:
                f(f"the review repeats {len(copied)} sentence(s) of the worker's sections verbatim; write your own review (first: {copied[0][:80]!r})")

    # 4. the new nodes
    all_ids = set(head_ids)
    new_nodes: dict[str, dict] = {}
    for p in new_paths:
        nid = pathlib.PurePosixPath(p).stem
        try:
            d = load_at("HEAD", p)
        except Exception as e:  # noqa: BLE001
            f(f"{p}: not valid JSON ({e})"); continue
        new_nodes[nid] = d
        if (d.get("created") or {}).get("item") != item:
            f(f"new node {nid}: created.item is {(d.get('created') or {}).get('item')!r}, not {item!r}")
        if nid in base_ids:
            f(f"new node {nid}: a node of this name already exists on {base} (choose another name or cite the existing node)")
        if d.get("id") not in (None, nid):
            f(f"new node {nid}: id field {d.get('id')!r} differs from the file name")
        st = str(d.get("status"))
        stmt = d.get("statement") or ""
        if not stmt.strip():
            f(f"new node {nid}: empty statement")
        else:
            cites = [c for c in CITE.findall(stmt) if c in all_ids]
            if not cites:
                f(f"new node {nid}: the statement cites no node ([def-...] / [lem-...] for every notion it uses)")
            if re.search(r"\((Idea|Proof|Sketch)\b|\bThe proof (uses|is|goes)|\bproof sketch\b", stmt, re.I):
                f(f"new node {nid}: the statement contains a proof sketch; a statement node states, the proof is the job of the worker who claims it (put the hint into source.place or a note)")
            if "⊗" in stmt or "→" in stmt:
                f(f"new node {nid}: unicode math symbols in the statement; write TeX (\\otimes, \\to)")
        if st == "unsplit":
            if d.get("proof"):
                f(f"new node {nid}: status unsplit but carries {len(d.get('proof'))} proof step(s); a new node is delivered without proof steps")
            if d.get("mathlib_match"):
                f(f"new node {nid}: status unsplit with a mathlib_match; set status mathlib if the match is exact")
        elif st == "mathlib":
            m = d.get("mathlib_match") or {}
            for k in ("declaration", "file", "line"):
                if not m.get(k):
                    f(f"new node {nid}: status mathlib but mathlib_match has no {k} (the line, verified with sed -n in the pinned Mathlib, is required)")
            if m.get("line") is not None and not isinstance(m.get("line"), int):
                f(f"new node {nid}: mathlib_match.line is not an integer")
        else:
            f(f"new node {nid}: status {st!r}; a new node is unsplit or mathlib")
        ms = d.get("mathlib_searches") or []
        kinds = {str(m.get("tool") or m.get("kind") or "").lower() for m in ms if isinstance(m, dict)}
        if len([m for m in ms if isinstance(m, dict) and m.get("query") and m.get("verdict")]) < 3 or len(kinds - {""}) < 3:
            f(f"new node {nid}: fewer than three kinds of Mathlib search with query and verdict (LeanSearch, Loogle/LeanFinder, grep of the Mathlib source)")
        for k in ("kind", "source", "title", "chapter", "unit"):
            if not d.get(k):
                f(f"new node {nid}: no {k}")
        if (d.get("blueprint") or {}).get("is") is not None:
            f(f"new node {nid}: blueprint.is is {(d.get('blueprint') or {}).get('is')!r}; a new node is no blueprint node, `is` is null (the maintainer sets it if the node turns out to be one)")
        extra = [k for k in MAINTAINER if k in d and k not in ("id", "kind", "title", "chapter", "unit", "source", "created", "lean_audit")]
        if extra:
            f(f"new node {nid}: carries the maintainer's field(s) {', '.join(extra)} (tools/README.md, 'Fields of a node'); a new node is delivered without them")
        for c in CITE.findall(stmt):
            if c not in all_ids:
                f(f"new node {nid}: cites [{c}], which is no node")
        form_checks(f, warns, f"new node {nid}", stmt)

    # 5. the item
    d = load_at("HEAD", item_path)
    if item in base_ids:
        try:
            b = load_at(base, base_ids[item])
        except Exception:  # noqa: BLE001
            b = None
        if b is not None:
            ch = changed_maintainer_fields(b, d)
            if ch:
                f(f"the item's maintainer's field(s) {', '.join(ch)} differ from {base} (check 9; tools/README.md 'Fields of a node'): take the node as it is on the base and set only the fields a split owns; an attachment goes into lean_candidates and the report, not into lean_audit")
    st = str(d.get("status"))
    is_def = str(d.get("kind", "")).startswith("def") or item.startswith("def-")
    if st == "mathlib" and d.get("mathlib_match"):
        pass
    elif st != "split":
        f(f"the item has status {st!r}, not split")
    if not d.get("split_report"):
        f("the item has no split_report")
    po = d.get("proof_origin") or {}
    if not is_def and (po.get("by") not in ("document", "agent") or not po.get("document")):
        f(f"proof_origin {po!r}: needs by (document|agent) and document")
    pf = d.get("proof")
    uses_all: list[str] = []
    if not is_def and st == "split":
        if not isinstance(pf, list) or not pf:
            f("the item has no proof steps")
    form_checks(f, warns, "the item's statement", d.get("statement") or "")
    for c in CITE.findall(d.get("statement") or ""):
        if c not in all_ids:
            f(f"the item's statement cites [{c}], which is no node (B3)")
    for k, s in enumerate(pf or [], 1):
        if not isinstance(s, dict) or not str(s.get("text", "")).strip():
            f(f"step {k}: no text"); continue
        form_checks(f, warns, f"step {k}", s.get("text") or "")
        for c in CITE.findall(s.get("text") or ""):
            if c not in all_ids:
                f(f"step {k}: cites [{c}] in its text, which is no node (C1)")
        if s.get("elementary") not in (True, False):
            f(f"step {k}: elementary must be true or false")
        uses = [u for u in (s.get("uses") or [])]
        if not uses and s.get("elementary") is not True:
            f(f"step {k}: cites no node and is not marked elementary")
        for u in uses:
            if u not in all_ids:
                f(f"step {k}: uses {u}, which is no node")
        uses_all += uses
        # 6. tags and section numbers in the step are carried by a cited node or by the item
        tags, secs = text_tokens(s.get("text"))
        cited_nodes = [load_at("HEAD", head_ids[u]) for u in uses if u in head_ids]
        for t in sorted(tags | secs):
            if any(carried(t, c) for c in cited_nodes):
                continue
            if carried(t, d):
                warns.append(f"step {k}: quotes {t}, carried only by the item itself (fine if it is the item's own source; if it is another lemma used here, cite a node that states it)")
            elif s.get("elementary") is True:
                warns.append(f"step {k}: elementary step quotes {t} with no node for it; accepted (rule of 2026-10-10 17:10 UTC: an elementary fact of two or three lines from the cited statements is a step, not a node; the reviewer judges whether it is elementary)")
            else:
                f(f"step {k}: quotes Stacks tag or lemma number {t}, which no cited node carries; cite a node that states it, or mark the step elementary if the fact is two or three lines from the cited statements (create a node only for a real lemma)")
    if pf and set(d.get("proof_deps") or []) != set(uses_all):
        f(f"proof_deps differ from the union of the steps' uses: {sorted(set(d.get('proof_deps') or []) ^ set(uses_all))}")
    for nid, nd in [(item, d)] + list(new_nodes.items()):
        stmt = nd.get("statement") or ""
        tags, secs = text_tokens(stmt)
        cited = [load_at("HEAD", head_ids[c]) for c in CITE.findall(stmt) if c in head_ids]
        own = {k: v for k, v in nd.items() if k != "statement"}
        for t in sorted(tags | secs):
            if not carried(t, own) and not any(carried(t, c) for c in cited):
                f(f"{'the item' if nid == item else 'new node ' + nid}: the statement quotes {t}, which neither its source nor a cited node carries")

    # 8. blueprint references (stages/1-dag.md §6)
    if not dirty:
        sys.path.insert(0, str(ROOT / "tools"))
        import blueprint_refs as br
        bnodes, _ = br.load()
        strict = {item, *new_nodes}
        for e in br.errors(bnodes, strict):
            if any(e.startswith(f"blueprint: {k} ") or e.startswith(f"blueprint: {k}:") for k in strict):
                f(e + " (coord/delivery-errors.md B9)")
        anc = br.ancestor_for_item(item, bnodes)
        for nid in new_nodes:
            fr = ((bnodes.get(nid) or {}).get("blueprint") or {}).get("from") or {}
            if isinstance(fr, dict) and fr.get("node") != anc:
                f(f"new node {nid}: blueprint.from.node is {fr.get('node')!r}; the item's nearest blueprint ancestor is {anc!r} (B9)")
        sr = d.get("split_report")
        if not (isinstance(sr, dict) and sr.get("blueprint")) and not (isinstance(sr, str) and "blueprint" in sr.lower()):
            f("the item's split_report has no 'blueprint' entry naming the places of the blueprint proof its steps realize (B9)")

    # 7. the scripts
    if not dirty:
        r = subprocess.run([sys.executable, "tools/review_split.py", item], cwd=ROOT, capture_output=True, text=True)
        out = (r.stdout + r.stderr).strip()
        if "PASS" not in out.splitlines()[0] if out else True:
            f("tools/review_split.py does not pass:\n   " + "\n   ".join(out.splitlines()[:12]))
        r = subprocess.run([sys.executable, "tools/check_dag.py"], cwd=ROOT, capture_output=True, text=True)
        # a "route:" warning counts only when it names the item or a new node; standing ones belong to the lead
        def findings(text):
            return [l for l in text.splitlines()
                    if l.startswith(("error", "unit", "cycle", "deps")) or "ERROR" in l
                    or (l.startswith("route") and any(i in l for i in [item, *new_nodes]))]
        bad = findings(r.stdout + r.stderr)
        # launcher's finding, 2026-10-10 15:30 UTC: the preflight fails only on what the delivery introduces. The findings
        # already present on the base are not the delivery's: they are computed on a temporary worktree of the base and
        # subtracted. (Pre-existing route warnings blocked thm-constructible-serre 29 times.)
        if bad:
            import tempfile, shutil
            wt = tempfile.mkdtemp(prefix="preflight-base-")
            try:
                subprocess.run(["git", "worktree", "add", "--detach", "-q", wt, base], cwd=ROOT, capture_output=True, text=True, check=True)
                rb = subprocess.run([sys.executable, "tools/check_dag.py"], cwd=wt, capture_output=True, text=True)
                on_base = set(findings(rb.stdout + rb.stderr))
                bad = [l for l in bad if l not in on_base]
            except subprocess.CalledProcessError as e:
                print(f"   (note: could not check the base {base} in a worktree: {e.stderr.strip()[:200]}; all findings count)")
            finally:
                subprocess.run(["git", "worktree", "remove", "--force", wt], cwd=ROOT, capture_output=True, text=True)
                shutil.rmtree(wt, ignore_errors=True)
        last = (r.stdout.strip().splitlines() or [""])[-1]
        if bad or "0 cycles" not in last:
            f("tools/check_dag.py reports a problem introduced by the delivery (findings already on the base are not counted):\n   " + "\n   ".join((bad or [last])[:12]))
    else:
        f("review_split.py and check_dag.py were not run because the working tree is not clean")

    print_result(fails, warns)
    return 1 if fails else 0


DOUBLED = re.compile(r"\\\\[A-Za-z]")
SETTING = re.compile(r"\b(in the setting of|as in the item|of the item above|the item's)\b", re.I)
PLAIN_ARROW = re.compile(r"(?<![\\$])(-->|->|=>)(?![a-z])")


def form_checks(f, warns: list[str], where: str, text: str) -> None:
    """coord/delivery-errors.md B2 and B4: a self-contained statement in TeX, written once."""
    if DOUBLED.search(text or ""):
        f(f"{where}: doubled backslashes (\\\\to, \\\\mathrm) in the JSON string; they render as literal backslashes, write one backslash per TeX command (B4)")
    m = SETTING.search(text or "")
    if m:
        f(f"{where}: {m.group(0)!r}: a node is read alone; introduce every object and hypothesis in the node itself (B2)")
    if PLAIN_ARROW.search(text or ""):
        warns.append(f"{where}: plain-text arrow ('->'); write TeX (\\to, \\Rightarrow) unless this is inside code (B4)")


def print_result(fails: list[str], warns: list[str] | None = None) -> None:
    if not fails:
        print("preflight OK: nothing the script can find; the mathematics is reviewed by the maintainer")
    else:
        print(f"preflight FAILED, {len(fails)} reason(s); do not push:")
        for i, x in enumerate(fails, 1):
            print(f"{i:2d}. {x}")
    for x in warns or []:
        print(f" ! {x}")


if __name__ == "__main__":
    try:
        sys.exit(main())
    except RuntimeError as e:
        print(f"error: {e}"); sys.exit(2)
