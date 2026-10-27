#!/usr/bin/env python3
"""Package and push one delivery in one command.

    python3 ~/weil-launcher-all/batch2/deliver.py <group> <item> [--no-push]

Reads the sandbox ~/weil-newtargets-sandbox/<group>/<item>/ (dag/nodes/<chapter>/<id>.json files and report.md),
builds one commit on the current origin/sheaf-dag in the group's clone, runs the repository's
preflight, pushes to deliver/<group>/<item>, and puts the clone back on sheaf-dag.
An existing node file is taken from origin and only the fields a split owns are set from the sandbox;
the maintainer's fields are kept as origin has them. Prints OK and the pushed commit, or the reason.
"""
import fcntl, json, os, pathlib, subprocess, sys
MAINT = {"id", "lean_audit", "reviewed", "created", "import_flags", "chapter", "unit", "merged_into", "target",
         "target_former", "lean", "lean_candidates", "lean_notes", "lean_names_rejected", "lead_note",
         "blueprint_kind", "blueprint_order", "blueprint_uses", "blueprint_lean", "blueprint_tags",
         "blueprint_notes", "blueprint_sketch", "blueprint_lean_not_found", "blueprint_proof_text",
         "blueprint_proof_steps", "uses_not_cited", "pointers"}
KEY = os.path.expanduser("~/weil_formal.pem")
ENV = dict(os.environ, GIT_SSH_COMMAND=f"ssh -i {KEY} -o StrictHostKeyChecking=no -o ServerAliveInterval=10")
def sh(*a, cwd, check=True, timeout=300):
    e = dict(ENV)
    # Delivery preflight must see the branch's item and new nodes; the live mirror is
    # the baseline used by workers and reviewers, while this working tree is the overlay.
    e["SHEAF_DAG"] = str(pathlib.Path(cwd) / "dag" / "nodes")
    r = subprocess.run(a, cwd=cwd, env=e, capture_output=True, text=True, timeout=timeout)
    if check and r.returncode:
        raise SystemExit(f"FAILED: {' '.join(a)}\n{r.stdout[-1500:]}{r.stderr[-1500:]}")
    return r

def citation_check(clone, sb, item, files):
    """Every citation of every proof step of the item must be backed by a verbatim quote from the cited node's statement."""
    import re
    norm = lambda t: re.sub(r"\s+", " ", t or "").strip()
    node = None
    for f in files:
        if f.stem == item: node = json.loads(f.read_text())
    if node is None or not isinstance(node.get("proof"), list): return []
    cf = sb / "citations.json"
    if not cf.exists(): return ["citations.json is missing in the sandbox (brief, step 4)"]
    try: cits = json.loads(cf.read_text())
    except Exception as e: return [f"citations.json is not valid JSON: {e}"]
    have = {(int(c.get("step", 0)), c.get("node")): norm(c.get("quote")) for c in cits if isinstance(c, dict)}
    def statement(nid):
        for f in files:
            if f.stem == nid: return norm(json.loads(f.read_text()).get("statement"))
        hits = list((clone / "dag" / "nodes").glob(f"*/{nid}.json"))
        return norm(json.loads(hits[0].read_text()).get("statement")) if hits else None
    bad = []
    for i, step in enumerate(node["proof"], 1):
        for nid in (step.get("uses") or []):
            q = have.get((i, nid)); stm = statement(nid)
            if stm is None: bad.append(f"step {i}: cited node {nid} does not exist (neither in the sandbox nor in the repository)"); continue
            if not q: bad.append(f"step {i}: no quote for the citation of {nid}"); continue
            if q not in stm: bad.append(f"step {i}: the quote for {nid} is not a verbatim part of that node's statement; open the node and copy the sentence the step uses"); continue
            if len(q) < min(40, len(stm)): bad.append(f"step {i}: the quote for {nid} is too short to show what the step takes from it (at least 40 characters, or the whole statement)")
    return bad

def search_check(clone, sb, files):
    """Every Mathlib search recorded in a NEW node must have been run with msearch.py (it is in searches.jsonl)."""
    import re
    norm = lambda t: re.sub(r"\s+", " ", str(t or "")).strip().lower()
    logf = sb / "searches.jsonl"; log = {}
    if logf.exists():
        for l in logf.read_text().split("\n"):
            try: r = json.loads(l); log[(norm(r["tool"]), norm(r["query"]))] = r
            except Exception: pass
    bad = []
    for f in files:
        if (clone / f.relative_to(sb)).exists(): continue          # an existing node: its searches were made earlier
        d = json.loads(f.read_text()); S_ = d.get("mathlib_searches") or []
        ran = set()
        for s_ in S_:
            if not isinstance(s_, dict): continue
            tool = norm(s_.get("tool")); tool = {"lean finder": "leanfinder", "lean_leanfinder": "leanfinder", "lean_leansearch": "leansearch", "lean_loogle": "loogle", "rg": "grep", "mathlib grep": "grep"}.get(tool, tool)
            q_ = norm(s_.get("query"))
            r = log.get((tool, q_))
            if r is None and tool == "grep":                           # a grep recorded as a whole command line: match on the pattern
                r = next((v for (t_, k_), v in log.items() if t_ == "grep" and k_ and k_ in q_), None)
            if r is None: bad.append(f"new node {f.stem}: the recorded {tool} search {str(s_.get('query'))[:70]!r} was not run with msearch.py (not in searches.jsonl); run it, read the hits, then write the verdict"); continue
            if r.get("ok"): ran.add(tool)
            elif "unavailable" not in norm(s_.get("verdict")) and "unavailable" not in norm(s_.get("results")): bad.append(f"new node {f.stem}: the {tool} service was unavailable for {str(s_.get('query'))[:50]!r}; record it as unavailable, not as 'no match'")
        if "grep" not in ran: bad.append(f"new node {f.stem}: no grep of the Mathlib source that ran (msearch.py ... grep)")
        if not (ran & {"leansearch", "leanfinder"}): bad.append(f"new node {f.stem}: no semantic search that ran (leanfinder; leansearch when it is up)")
        if "loogle" not in ran and len(ran & {"leansearch", "leanfinder"}) < 2: bad.append(f"new node {f.stem}: needs a loogle search that ran (or both semantic searches)")
    return bad
def dup_check(clone, sb, item, files, rep):
    """A new node that carries the Stacks tag of an existing node (or of its own item) must be told apart from it in the report."""
    import re
    def tags(d):
        source = json.dumps((d or {}).get("source") or "")
        # Remove complete arXiv identifiers before looking for Stacks tags:
        # 0810.2340 is a paper identifier, not a reference to Stacks tag 0810.
        source = re.sub(r"\b[0-9]{2}(?:0[1-9]|1[0-2])\.[0-9]{4,5}(?:v[0-9]+)?\b", "", source)
        return set(re.findall(r"\b0[0-9A-Z]{3}\b", source))
    new = {}; itemnode = None
    for f in files:
        try: d = json.loads(f.read_text())
        except Exception: continue                                   # reported as invalid JSON further on
        if f.stem == item: itemnode = d
        elif not (clone / f.relative_to(sb)).exists(): new[f.stem] = d
    if not new: return []
    want = set().union(*[tags(d) for d in new.values()])
    if not want: return []
    idx = {}
    for f in (clone / "dag" / "nodes").glob("*/*.json"):
        t = f.read_text()
        if not any(w in t for w in want): continue
        try: d = json.loads(t)
        except Exception: continue
        if d.get("status") == "merged": continue
        for w in tags(d) & want: idx.setdefault(w, []).append(f.stem)
    lines = rep.read_text().split("\n"); bad = []
    nonel = [st for st in (itemnode or {}).get("proof") or [] if isinstance(st, dict) and st.get("elementary") is not True]
    for nid, d in new.items():
        hits = []
        for w in sorted(tags(d)):
            for h in idx.get(w, []):
                if h != nid and h not in new and h not in [x for x, _ in hits]: hits.append((h, w))
        hits.sort(key=lambda x: x[0] != item); hits = hits[:12]
        if itemnode is not None and tags(d) & tags(itemnode) and len(nonel) == 1 and nid in (nonel[0].get("uses") or []):
            bad.append(f"new node {nid} has the Stacks tag of the item, and the item's proof has a single non-elementary step that cites it: the content of the item was moved into a new node (delivery-errors D1, D2). Write the proof of the item in steps instead.")
        miss = [(h, w) for h, w in hits if not any(nid in l and h in l for l in lines)]
        if miss:
            bad.append(f"new node {nid} has the same Stacks tag as existing node(s) " + ", ".join(f"{h} ({w})" for h, w in miss) + ". Open each. If one states the fact (or the fact is a special case of it), cite that node and delete the new one. If the new node is a clause of the item itself, it is not a split: prove the clause in steps. Otherwise add to report.md, under '## Not duplicates', one line per pair naming both ids and the difference of the statements, e.g. '" + nid + " vs " + miss[0][0] + ": <difference>'.")
    return bad

def merge_split_node(base, new, split_owns, blueprint_owns):
    """Overlay only the fields the stage-1 contract permits a worker to set.

    Unknown fields are maintainer-owned too; an explicit MAINTAINER list cannot
    protect metadata added after that list was written (e.g. blueprint_snapshot).
    """
    keep_new = {"id", "kind", "title", "chapter", "unit", "source", "created"}
    if base is None:
        out = {k: v for k, v in new.items() if k in split_owns or k in keep_new}
        if isinstance(new.get("blueprint"), dict):
            out["blueprint"] = {k: v for k, v in new["blueprint"].items() if k in blueprint_owns}
            out["blueprint"]["is"] = None
        return out
    out = dict(base)
    for k, v in new.items():
        if k == "blueprint" and isinstance(v, dict):
            b = dict(base.get("blueprint") or {})
            b.update({x: y for x, y in v.items() if x in blueprint_owns})
            out[k] = b
        elif k in split_owns:
            out[k] = v
    return out

def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--") and a != "."]
    if len(args) != 2: raise SystemExit(__doc__)
    g, item = args; push = "--no-push" not in sys.argv
    import stage1_request
    return stage1_request.run(g, item, push, deliver)


def deliver(g, item, push):
    sys.path.insert(0, "/home/ubuntu/weil-launcher-all"); import sharedrepo   # 2026-10-16: no clone per group
    # 2026-10-17 (io2): no worktree and no worktree slot. The checks read origin's tree from the object store, the
    # commit is built with a temporary index (nocheckout.build) and bundled from a tiny view repository; a real
    # worktree is made only for srvpreflight's local fallback.
    import nocheckout
    print(f"Preparing stage-1 delivery {g}/{item}", flush=True)
    sb = pathlib.Path.home() / "weil-newtargets-sandbox" / g / item
    sharedrepo.fetch("weil-conjectures-sheaf")
    tree = nocheckout.Tree("weil-conjectures-sheaf", nocheckout.resolve("weil-conjectures-sheaf", "origin/sheaf-dag")); clone = tree.path()
    files = sorted(sb.glob("dag/nodes/*/*.json")); rep = sb / "report.md"
    if not files: raise SystemExit(f"FAILED: no node files under {sb}/dag/nodes/")
    if not rep.exists() or f"## Review by {g}" not in rep.read_text():
        raise SystemExit(f"FAILED: {rep} is missing or has no '## Review by {g}' section")
    if False and push and (sb / '.brief5').exists() and not (sb / '.check').exists():   # 2026-10-17 nocheck
        raise SystemExit("NOT PUSHED: this split is handed to a second reader, who delivers it. Your dry run is your last step: answer READY.")
    if push and (sb / '.check').exists() and f"## Second reading by {g}" not in rep.read_text():
        raise SystemExit(f"FAILED: report.md has no '## Second reading by {g}' section")
    import stage1_handoff
    handoff_inputs = stage1_handoff.fingerprint(sb)
    ilock = sharedrepo.WT / "locks" / "none.index.lock"
    if ilock.exists() and __import__('time').time() - ilock.stat().st_mtime > 180:
        if subprocess.run(["fuser", "-s", str(ilock)]).returncode != 0:
            ilock.unlink(missing_ok=True)
    bad = citation_check(clone, sb, item, files) if ((sb / '.brief2').exists() or (sb / 'citations.json').exists()) else []
    if (sb / '.brief3').exists() or (sb / 'searches.jsonl').exists():
        sbad = search_check(clone, sb, files)
        if sbad:
            print("SEARCH CHECK FAILED, nothing pushed. Mathlib searches are made only with /home/ubuntu/weil-launcher-all/batch2/msearch.py and recorded as they came out:\n " + "\n ".join(sbad[:40])); sys.exit(1)
    if (sb / '.brief4').exists():
        dbad = dup_check(clone, sb, item, files, rep)
        if dbad:
            print("DUPLICATE CHECK FAILED, nothing pushed:\n " + "\n ".join(dbad[:40])); sys.exit(1)
    if bad:
        print("CITATION CHECK FAILED, nothing pushed. For every node a step cites, the step may use only what that node's statement says. Repair the split (cite the node that really states the fact, or create a statement node for it) and citations.json, then run again:\n " + "\n ".join(bad[:40])); sys.exit(1)
    sharedrepo.fetch("weil-conjectures-sheaf")
    br = f"deliver/{g}/{item}"
    delivery_base = nocheckout.resolve("weil-conjectures-sheaf", "origin/sheaf-dag")
    if delivery_base != tree.base:
        tree = nocheckout.Tree("weil-conjectures-sheaf", delivery_base); clone = tree.path()
    shared = sharedrepo.shared("weil-conjectures-sheaf")
    added = {}; skipped = []
    sys.path.insert(0, str(nocheckout.extract(tree, "tools/node_fields.py") / "tools"))
    from node_fields import SPLIT_OWNS, SPLIT_OWNS_BLUEPRINT
    for f in files:
        rel = f.relative_to(sb); dst = clone / rel
        try: new = json.loads(f.read_text())
        except Exception as e: raise SystemExit(f"FAILED: {rel} is not valid JSON: {e}")
        if dst.exists():
            base = json.loads(dst.read_text())
            cur = merge_split_node(base, new, SPLIT_OWNS, SPLIT_OWNS_BLUEPRINT)
            if cur == base:
                # an unchanged copy of an existing node (kept in the sandbox for reading): not part of the delivery
                if f.stem != item: skipped.append(f.stem)
                continue
            out = cur
        else:
            out = merge_split_node(None, new, SPLIT_OWNS, SPLIT_OWNS_BLUEPRINT)
            # New nodes carry the worker's creation stamp (brief-stage1 §3).
            # Existing nodes still retain the origin stamp in the branch above.
            created = dict(out["created"]) if isinstance(out.get("created"), dict) else {}
            created.setdefault("item", item)
            out["created"] = created
        added[str(rel)] = json.dumps(out, ensure_ascii=False, indent=1) + "\n"
    if skipped: print("note: unchanged copies of existing nodes left out:", ", ".join(skipped))
    # A key node also realizes its unit: the stage-1 contract permits these two fields.
    item_node = next((json.loads(f.read_text()) for f in files if f.stem == item), {})
    for f in sorted((sb / "dag/units").glob("*.json")):
        if f.stem != item_node.get("unit"):
            raise SystemExit(f"FAILED: unit {f.stem} is not this item's unit")
        rel = f.relative_to(sb); dst = clone / rel
        cur = json.loads(dst.read_text()); new = json.loads(f.read_text())
        for k in ("realized", "realized_by"):
            if k in new: cur[k] = new[k]
        added[str(rel)] = json.dumps(cur, ensure_ascii=False, indent=1) + "\n"
    added[f"coord/reports/{g}/{item}.md"] = rep.read_text()
    commit, _ = nocheckout.build("weil-conjectures-sheaf", delivery_base, added, f"Split {item}", env=ENV, tree=tree)
    if not commit:
        raise SystemExit("FAILED: nothing differs from origin/sheaf-dag (already merged, or the sandbox holds no change)")
    # 2026-10-17 (srvpreflight): the preflight runs on the Weil server on the same commit and base; local fallback
    import srvpreflight
    view = nocheckout.view("weil-conjectures-sheaf", commit, delivery_base)
    _pe = dict(ENV); _pe["SHEAF_DAG"] = str(pathlib.Path(view) / "dag" / "nodes")
    _cmd = ["python3", "tools/preflight_delivery.py", g, item, "--base", delivery_base]
    p = srvpreflight.run("weil-conjectures-sheaf", view, _cmd, _pe, timeout=600,
                         local_cmd=nocheckout.fallback_cmd("weil-conjectures-sheaf", commit, _cmd, ("lean",)))
    if p.returncode:
        print("PREFLIGHT FAILED, nothing pushed. Repair in the sandbox and run this command again:\n" + (p.stdout + p.stderr)[-4000:]); sys.exit(1)
    head = nocheckout.short("weil-conjectures-sheaf", commit)
    if push:
        sharedrepo.fetch("weil-conjectures-sheaf")
        same = nocheckout.same_delivery("weil-conjectures-sheaf", commit, br)   # 2026-10-17 (churn)
        if same:
            print(f"OK {br} is already at {same[:10]} with exactly this content; nothing pushed (a re-push would only restart its review). Wait for the review."); return
        sh("env", "GIT_SSH_COMMAND=/home/ubuntu/weil-launcher-all/gitssh_v2.sh", "git", "-c", "ssh.variant=ssh", "-c", "protocol.version=2", "-c", "push.negotiate=true", "push", "-q", "-f", "origin", f"{commit}:refs/heads/{br}", cwd=shared, timeout=180)
        print(f"OK pushed {br} at {head} ({len(files)} node file(s) + report). Wait for the merge; delete the sandbox when coord/returns/{g}.md stays clear and the item is merged.")
    else:
        if stage1_handoff.record_ready(sb, g, item, head, handoff_inputs):
            print("Saved durable stage-1 dry-run receipt for the second-reader handoff.", flush=True)
        print(f"OK (not pushed) {br} at {head}: preflight passed")
if __name__ == "__main__": main()
