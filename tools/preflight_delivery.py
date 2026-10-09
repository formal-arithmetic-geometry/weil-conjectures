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
     by a cited node (or by the node itself); a step that only quotes a tag fails;
  7. tools/review_split.py <item> passes and tools/check_dag.py reports no cycle, route or
     dependency error.
"""
from __future__ import annotations
import json, pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
TAG = re.compile(r"(?<![A-Za-z0-9])0[0-9A-Z]{3}(?![A-Za-z0-9])")
SECTION = re.compile(r"(?<![\d.])\d{1,2}\.\d{1,3}\.\d{1,3}(?![\d.])")
CITE = re.compile(r"\[([a-z][a-z0-9-]+)\]")


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


def main() -> int:
    args: list[str] = []
    base = "origin/sheaf-dag"
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
        for c in CITE.findall(stmt):
            if c not in all_ids:
                f(f"new node {nid}: cites [{c}], which is no node")

    # 5. the item
    d = load_at("HEAD", item_path)
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
    for k, s in enumerate(pf or [], 1):
        if not isinstance(s, dict) or not str(s.get("text", "")).strip():
            f(f"step {k}: no text"); continue
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
            else:
                f(f"step {k}: quotes Stacks tag or lemma number {t}, which no cited node carries; cite a node that states it (create it unsplit if none exists)")
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

    # 7. the scripts
    if not dirty:
        r = subprocess.run([sys.executable, "tools/review_split.py", item], cwd=ROOT, capture_output=True, text=True)
        out = (r.stdout + r.stderr).strip()
        if "PASS" not in out.splitlines()[0] if out else True:
            f("tools/review_split.py does not pass:\n   " + "\n   ".join(out.splitlines()[:12]))
        r = subprocess.run([sys.executable, "tools/check_dag.py"], cwd=ROOT, capture_output=True, text=True)
        bad = [l for l in (r.stdout + r.stderr).splitlines() if l.startswith(("error", "unit", "route", "cycle", "deps")) or "ERROR" in l]
        last = (r.stdout.strip().splitlines() or [""])[-1]
        if bad or "0 cycles" not in last:
            f("tools/check_dag.py reports a problem:\n   " + "\n   ".join((bad or [last])[:12]))
    else:
        f("review_split.py and check_dag.py were not run because the working tree is not clean")

    print_result(fails, warns)
    return 1 if fails else 0


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
