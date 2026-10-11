#!/usr/bin/env python3
"""Merge the delivery of a group on another machine (roles/maintainer.md §7, roles/remote-lead.md).

Usage (from the project root; by the lead, or by a reviewer sub-agent of the lead after its review):
  tools/merge_delivery.py list                          the delivery branches refs/heads/deliver/<group>/<item>
  tools/merge_delivery.py show <group> <item>           print the delivery for reading (spot check), merge nothing
  tools/merge_delivery.py <group> <item> [options]      check, merge by files, verify, mark reviewed, close the claim,
                                                        write the ledger line, commit, delete the branch
      --spot-checked NOTE   what the reviewer checked (goes into `reviewed`)
      --reviewer ID         the reviewer sub-agent (default "reviewer"); named in the commit message and the ledger
      --apply-fixes DIR     the reviewer's corrected files DIR/dag/nodes/<chapter>/<id>.json (whole files): the fields a
                            split owns are taken; since 15:05 UTC a file there that is a NEW node (on neither branch) is
                            added as a statement-only node (status unsplit, created.item = item): "FIX more, RETURN less"
                            split owns are taken from them (a new node of the delivery is taken whole); never a
                            maintainer's field, never a file outside the delivery
      --tool-uses a,b,c     added to the item's `tool_uses` before review_split.py runs (the worker's split_report.tool_uses
                            declarations are copied too; --drop-tool-uses a,b leaves out the ones the reviewer rejects)
      --drop-nodes a,b      delivered NEW nodes not to merge (duplicates of existing nodes); the fixes must drop their citations
      --reviewed NOTE       the `reviewed` note (default: the mechanical-checks note, with the spot check)
      --lead-note TEXT      appended to the item's `lead_note`
      --verdict PASS|FIX    for the ledger line (default FIX with --apply-fixes, else PASS)
      --head SHA            refuse unless the branch head is SHA (the commit the reviewer read)
  tools/merge_delivery.py <group> <item> --stage 2 --reviewer ID --head SHA [--apply-fixes DIR] [--spot-checked NOTE]
                        [--drop-nodes ID[,ID...]] [--verdict PASS|FIX] [--dry-run]
                                                        a stage-2 delivery (tools/README.md "Stage 2"): the mechanical
                        checks of tools/stage2_delivery.py (item, new definition nodes, dependency nodes: coord/STATE.md
                        "STAGE 2 EXTRA NODES"); with several modules, those importing no sibling are compiled first in
                        lean/.sandbox/L/ (a failure aborts, nothing landed); then every module, in dependency order
                        (sibling imports first), written to lean/.sandbox/L/<node>.lean and landed with
                        `SHEAF_GROUP=L tools/land.sh` (the first failing: nothing changed; a later one: the tool STOPS,
                        commits nothing and prints the landings to revert with `tools/landing.py revert <id> <reason>`);
                        `lean` (statement re-read from the landed file) and `reviewed_lean` set on the item (and its
                        stmt_deps gain the new nodes) and on each dependency node; each new node written whole with
                        `reviewed` {date, by L, reviewer, group, result, note: "new definition node of a stage-2
                        delivery, read against its source by the reviewer"} and `reviewed_lean`; the report; the same
                        bookkeeping as stage 1; one commit "State <item> (<group>, reviewed by <ID>); new nodes: <ids>".
                        --dry-run prints what it would do, changes nothing. A stage-2 DIR holds any of: <basename>.lean
                        (a fixed module of the delivery, any of them; its node's lean.statement re-read from it,
                        lean.declarations filtered to the names it declares; refused if lean.declaration is not in it,
                        unless the record file renames it), <item>.lean-record.json (keys merged over the item's `lean`,
                        theirs winning; `by`, `date` stay), <new node id>.json (replaces that new node file whole),
                        <item>.report.md (replaces the report), <item>.statement-change.json (replaces the item's
                        statement_change). A changed record gets `fixed_by: <ID>`; the whole delivery is checked
                        again on the fixed versions. A CORRECTED item (coord/STATE.md, STAGE 2 STATEMENT CORRECTION;
                        node_fields.check_statement_change) gets statement, stmt_deps, proof, proof_deps and
                        statement_change from the branch (refused if they moved on sheaf-dag since the base), and
                        `reviewed_lean.statement_corrected: true`. --drop-nodes ID[,ID...] (stage 2): each ID must be a
                        NEW node of the delivery (a duplicate of a landed node); its node file and every module whose
                        only owner it is are left out, the item's stmt_deps/proof_deps lose it, the fixes (DIR) repoint
                        the item's module and record at the landed declaration; the checks run on the result;
                        reviewed_lean.note, the ledger line and the commit message name the dropped ids.
  tools/merge_delivery.py return <group> <item> REASONS write the reasons into coord/returns/<group>.md, the ledger
                                                        line, and commit; the claim and the branch stay with the group

Output: exactly one line, `MERGED <item> <commit>` / `RETURNED <item> <commit>`, or `NOT MERGED <item>: <reason>`
(`NOT RETURNED ...` for a return) with exit code 1.

Every path that writes the working tree or commits holds an exclusive flock on coord/.merge.lock (not committed), so
several reviewers can run the tool at once; the lead's own commits can take it too: `flock coord/.merge.lock git ...`.
The tool itself is NEVER run under `flock coord/.merge.lock`: it gives up after SHEAF_LOCK_TIMEOUT (120) s naming the holder.

The merge works by files on the current tip, never by cherry-pick, so it cannot conflict: (1) the branch is based on
sheaf-dag and its base is at most SHEAF_DELIVERY_MAX_AGE_HOURS old (default 48); (2) it changes only the item's node,
new node files created by the item, the realized fields of the item's unit record, and coord/reports/<group>/<item>.md,
which must carry "## Review by <group>"; (3) a new node and the report are copied from the branch; the item's node and
the unit record are taken as they are on HEAD and only the fields a split owns (tools/node_fields.py: SPLIT_OWNS, and
blueprint.from / blueprint.same_as; realized / realized_by on the unit record) are set from the branch, where the
branch changed them against its base; (4) the fixes, tool_uses; (5) review_split.py and check_dag.py pass; (6)
`reviewed` is written, the claim closed, the return entry dropped, the ledger line appended, one commit made with the
delivery's author; the branch is deleted, and the queue rewritten when coord/queue.tsv is older than 60 s. On any
failure the delivery's files are put back as on HEAD (new files removed) and nothing is committed.
"""
import glob, os as _os, sys as _sys
if _os.environ.get("SHEAF_LEAD") != "L-only":
    _sys.stderr.write("merge_delivery.py: refused. This tool is run only by the lead L in the lead's shell (deliveries are merged after review). Remote groups: push deliver/<group>/<item> and wait; any merge not made by L is reverted. Reported to the human in coord/HUMAN.md.\n")
    _sys.exit(2)

import argparse
import contextlib
import datetime
import fcntl
import io
import json
import pathlib
import re
import subprocess
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import leanindex as li  # noqa: E402
from node_fields import SPLIT_OWNS, SPLIT_OWNS_BLUEPRINT, STAGE2_ITEM_CORRECTION  # noqa: E402

ROOT = li.ROOT
MAIN = "sheaf-dag"
MAX_AGE = float(li.config().get("SHEAF_DELIVERY_MAX_AGE_HOURS", "48")) * 3600
LOCK = ROOT / "coord" / ".merge.lock"
UNIT_OWNS = ("realized", "realized_by")

BLUEPRINT_RULE = "28935e1a0b"  # the commit that introduced the blueprint field (2026-10-10)


class Fail(RuntimeError):
    pass


def git(*a, check=True):
    r = subprocess.run(["git", *a], cwd=ROOT, text=True, capture_output=True)
    if check and r.returncode != 0:
        raise Fail(f"git {' '.join(a[:3])}{' ...' if len(a) > 3 else ''} failed: {(r.stderr or r.stdout).strip()}")
    return (r.stdout or "").strip()


def git_retry(*a):
    """add / commit: one retry after 2 s on a failure (index.lock held by another git, a file changed meanwhile)."""
    try:
        return git(*a)
    except Fail:
        time.sleep(2)
        return git(*a)


@contextlib.contextmanager
def merge_lock():
    """coord/.merge.lock, given up after SHEAF_LOCK_TIMEOUT (120) s with the holder named: never run this tool
    under `flock coord/.merge.lock`, it would wait for itself."""
    import mergelock
    try:
        cm = mergelock.merge_lock(LOCK)
        cm.__enter__()
    except mergelock.LockTimeout as e:
        raise Fail(str(e))
    try:
        yield
    finally:
        cm.__exit__(None, None, None)


def branch_of(group, item):
    return f"deliver/{group}/{item}"


def has_ref(ref):
    return subprocess.run(["git", "rev-parse", "--verify", "-q", ref], cwd=ROOT, capture_output=True).returncode == 0


def node_path(item):
    hits = list((ROOT / "dag" / "nodes").glob(f"*/{item}.json"))
    return hits[0].relative_to(ROOT).as_posix() if hits else None


def load_json_at(ref, path):
    return json.loads(git("show", f"{ref}:{path}"))


def exists_at(ref, path):
    return subprocess.run(["git", "cat-file", "-e", f"{ref}:{path}"], cwd=ROOT, capture_output=True).returncode == 0


def dump(d):
    return json.dumps(d, indent=1, ensure_ascii=False) + "\n"


def now_hm():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%H:%M")


def today():
    return datetime.datetime.now(datetime.timezone.utc).date().isoformat()


def ledger_line(text):
    line = f"- {now_hm()} L: {text}\n"
    with open(ROOT / "coord" / "ledger.md", "a") as f:
        f.write(line)
    return line


def remove_line(path, line):
    """Undo an append of `line` (the last occurrence), leaving lines others appended meanwhile."""
    if not path.exists():
        return
    t = path.read_text()
    i = t.rfind(line)
    if i >= 0:
        path.write_text(t[:i] + t[i + len(line):])


def return_entries(group, item):
    p = ROOT / "coord" / "returns" / f"{group}.md"
    if not p.exists():
        return p, None, []
    t = p.read_text()
    parts = re.split(r"(?m)^(?=## )", t)
    return p, t, parts


def cmd_list():
    out = git("for-each-ref", "--format=%(refname:short)\t%(committerdate:iso-strict)\t%(objectname:short)", "refs/heads/deliver/")
    if not out:
        print("no deliveries"); return 0
    for l in out.splitlines():
        ref, date, sha = l.split("\t")
        parts = ref.split("/")
        group, item = parts[1], "/".join(parts[2:])
        lock = ROOT / "coord" / "claims" / f"{item}.lock"
        who = json.loads(lock.read_text()).get("who") if lock.exists() else "no claim"
        print(f"{ref}\t{date}\t{sha}\tclaim: {who}")
    return 0


def inspect(group, item):
    """Steps 1 and 2: returns (base, commits, kinds) or raises with the reason."""
    br = branch_of(group, item)
    if not has_ref(f"refs/heads/{br}"):
        raise Fail(f"no branch {br}")
    base = git("merge-base", MAIN, br)
    age = time.time() - int(git("show", "-s", "--format=%ct", base))
    if age > MAX_AGE:
        raise Fail(f"base {base[:7]} is {age/3600:.0f} h behind {MAIN}: pull {MAIN}, rebase, push again")
    commits = git("rev-list", "--reverse", f"{base}..{br}").split()
    if not commits:
        raise Fail("the branch has no commit beyond its base")
    if len(commits) > 3:
        raise Fail(f"{len(commits)} commits: deliver one item as one commit (squash)")
    files = git("diff", "--name-only", base, br).splitlines()
    item_path = node_path(item)
    if item_path is None or not exists_at(base, item_path):
        raise Fail(f"the item {item} has no node file at the base")
    unit = load_json_at(base, item_path).get("unit")
    report = f"coord/reports/{group}/{item}.md"
    kinds = {}
    for f in files:
        if not exists_at(br, f):
            raise Fail(f"the delivery deletes {f}")
        if f == item_path:
            kinds[f] = "item"
        elif f == report:
            kinds[f] = "report"
        elif f.startswith("dag/nodes/") and f.endswith(".json") and not exists_at(base, f):
            d = load_json_at(br, f)
            if (d.get("created") or {}).get("item") != item:
                raise Fail(f"new node {f} has created.item != {item}")
            kinds[f] = "new"
        elif unit and f == f"dag/units/{unit}.json":
            a, b = load_json_at(base, f), load_json_at(br, f)
            for k in UNIT_OWNS:
                a.pop(k, None); b.pop(k, None)
            if a != b:
                raise Fail(f"{f}: only the realized fields may change")
            kinds[f] = "unit"
        else:
            raise Fail(f"file outside the item's files: {f}")
    if "item" not in kinds.values():
        raise Fail("the item's node file is unchanged")
    if "report" not in kinds.values():
        raise Fail(f"no report file {report}")
    if f"## Review by {group}" not in git("show", f"{br}:{report}"):
        raise Fail(f"the report lacks the heading '## Review by {group}' (the group's own review)")
    return base, commits, kinds


def cmd_show(group, item):
    base, commits, kinds = inspect(group, item)
    br = branch_of(group, item)
    print(f"branch {br}: {len(commits)} commit(s) on base {base[:7]}; files: {kinds}")
    print(git("show", "--stat", "--format=%an <%ae> %ci%n%s%n%b", *commits))
    print("\n===== report =====")
    print(git("show", f"{br}:coord/reports/{group}/{item}.md"))
    for f, k in kinds.items():
        if k in ("item", "new"):
            d = load_json_at(br, f)
            print(f"\n===== {k}: {f} =====\nstatus {d.get('status')}; unit {d.get('unit')}\n{d.get('statement')}")
            for i, s in enumerate(d.get("proof") or []):
                print(f"-- step {i+1} uses={s.get('uses')} elementary={s.get('elementary')}\n{s.get('text')}")
            if d.get("mathlib_match"):
                print("mathlib_match:", d["mathlib_match"])
    return 0


# ---------------------------------------------------------------- merge by files

def set_owned(cur, src, owns, bp_owns=(), ref=None):
    """`cur` with the fields in `owns` (and blueprint.<bp_owns>) taken from `src`. With `ref` (the branch's base
    version) only the fields that `src` changed against `ref` are taken (a three-way merge per field)."""
    out = dict(cur)
    changed = (lambda k, a, b: a.get(k, KeyError) != b.get(k, KeyError)) if ref is not None else (lambda *_: True)
    for k in owns:
        if not changed(k, src, ref):
            continue
        if k in src:
            out[k] = src[k]
        else:
            out.pop(k, None)
    if bp_owns:
        sb = src.get("blueprint") or {}
        rb = (ref.get("blueprint") or {}) if ref is not None else None
        b = dict(out.get("blueprint") or {"is": None})
        for k in bp_owns:
            if rb is not None and not changed(k, sb, rb):
                continue
            if k in sb:
                b[k] = sb[k]
            else:
                b.pop(k, None)
        if b != {"is": None} or "blueprint" in out:
            out["blueprint"] = b
    return out


class Tree:
    """The files the merge writes, so that a failure puts each back as it is on HEAD."""

    def __init__(self):
        self.touched = []   # existing on HEAD
        self.created = []   # absent on HEAD

    def write(self, rel, text):
        p = ROOT / rel
        if exists_at("HEAD", rel):
            if rel not in self.touched:
                self.touched.append(rel)
        elif rel not in self.created:
            self.created.append(rel)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)

    def restore(self):
        if self.touched:
            subprocess.run(["git", "checkout", "HEAD", "--", *self.touched], cwd=ROOT, capture_output=True)
        for rel in self.created:
            subprocess.run(["git", "rm", "-q", "--cached", "--ignore-unmatch", "--", rel], cwd=ROOT, capture_output=True)
            (ROOT / rel).unlink(missing_ok=True)
            d = (ROOT / rel).parent
            while d != ROOT and d.is_dir() and not any(d.iterdir()):
                d.rmdir(); d = d.parent


def merge_files(group, item, base, kinds, tree):
    br = branch_of(group, item)
    for f, k in kinds.items():
        if k == "report":
            tree.write(f, subprocess.run(["git", "show", f"{br}:{f}"], cwd=ROOT, text=True, capture_output=True, check=True).stdout)
        elif k == "new" and not exists_at("HEAD", f):
            nd = load_json_at(br, f)
            c = nd.get("created") if isinstance(nd.get("created"), dict) else {"item": item}
            c.setdefault("by", "worker"); c.setdefault("date", today()); nd["created"] = c   # maintainer fields, filled at merge
            tree.write(f, dump(nd))
        elif k in ("item", "new"):
            head = load_json_at("HEAD", f)
            if k == "new" and (head.get("created") or {}).get("item") != item:
                raise Fail(f"new node {f} exists on {MAIN} already, created for {(head.get('created') or {}).get('item')}: rename it")
            ref = load_json_at(base, f) if exists_at(base, f) else {}
            tree.write(f, dump(set_owned(head, load_json_at(br, f), SPLIT_OWNS, SPLIT_OWNS_BLUEPRINT, ref)))
        elif k == "unit":
            tree.write(f, dump(set_owned(load_json_at("HEAD", f), load_json_at(br, f), UNIT_OWNS, (), load_json_at(base, f))))


def apply_fixes(fixdir, kinds, tree, item=None, group=None):
    """Returns (files fixed, statement nodes added by the reviewer). Since 2026-10-10 15:05 UTC (decision of the human:
    "FIX more, RETURN less") a fix may ADD an unsplit statement-only node under dag/nodes/ that is neither on the main
    branch nor on the delivery branch: created.item must be the item, status "unsplit", proof empty; it enters the queue."""
    fixdir = pathlib.Path(fixdir).resolve()
    if not fixdir.is_dir():
        raise Fail(f"--apply-fixes {fixdir}: no such directory")
    n = 0
    added = 0
    for p in sorted(fixdir.rglob("*")):
        if not p.is_file():
            continue
        rel = p.relative_to(fixdir).as_posix()
        if not (rel.startswith(("dag/nodes/", "dag/units/")) and rel.endswith(".json")):
            raise Fail(f"fix {rel}: only dag/nodes/... and dag/units/... files can be fixed")
        try:
            fx = json.loads(p.read_text())
        except json.JSONDecodeError as e:
            raise Fail(f"fix {rel}: not JSON ({e})")
        if rel not in kinds:
            br = branch_of(group, item) if group and item else None
            if not rel.startswith("dag/nodes/") or exists_at("HEAD", rel) or (br and exists_at(br, rel)):
                raise Fail(f"fix {rel}: not a file of the delivery (a fix only adds a NEW statement node; it never touches another node)")
            if any(glob.glob(str(ROOT / "dag" / "nodes" / "*" / pathlib.Path(rel).name))):
                raise Fail(f"fix {rel}: a node with this id exists in another chapter")
            if fx.get("id") != pathlib.Path(rel).stem or (fx.get("created") or {}).get("item") != item:
                raise Fail(f"fix {rel}: a reviewer-added node needs id = file stem and created.item = {item}")
            if fx.get("status") != "unsplit" or fx.get("proof") not in ([], None) or not fx.get("statement") or not fx.get("stmt_deps"):
                raise Fail(f"fix {rel}: a reviewer-added node is statement-only: status unsplit, empty proof, a statement citing nodes, stmt_deps")
            tree.write(rel, dump(fx))
            kinds[rel] = "new"
            n += 1; added += 1
            continue
        cur = json.loads((ROOT / rel).read_text())
        if kinds[rel] == "new" and not exists_at("HEAD", rel):
            if fx.get("id") != cur.get("id") or (fx.get("created") or {}).get("item") != (cur.get("created") or {}).get("item"):
                raise Fail(f"fix {rel}: id or created.item differ from the delivered new node")
            fx["created"] = cur.get("created")   # the maintainer's stamp (by/date filled at merge) wins
            tree.write(rel, dump(fx))
        elif kinds[rel] == "unit":
            tree.write(rel, dump(set_owned(cur, fx, UNIT_OWNS)))
        else:
            tree.write(rel, dump(set_owned(cur, fx, SPLIT_OWNS, SPLIT_OWNS_BLUEPRINT)))
        n += 1
    return n, added


def backfill_blueprint(ids):
    """tools/blueprint_refs.py backfill, written only on the delivered nodes (the rest of the tree is not touched)."""
    import blueprint_refs as bp

    class Sink:
        def write_text(self, *a, **k):
            pass

    nodes, paths = bp.load()
    keep = {i: (p if i in ids else Sink()) for i, p in paths.items()}
    orig = bp.load
    bp.load = lambda: (nodes, keep)
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            bp.backfill()
    finally:
        bp.load = orig


def edit_json(tree, rel, fn):
    d = json.loads((ROOT / rel).read_text())
    fn(d)
    tree.write(rel, dump(d))


def cmd_merge(o):
    group, item = o.group, o.item
    br = branch_of(group, item)
    if git("symbolic-ref", "-q", "--short", "HEAD", check=False) != MAIN:
        raise Fail(f"the working tree is not on {MAIN}")
    with merge_lock():
        base, commits, kinds = inspect(group, item)
        if o.head and not git("rev-parse", br).startswith(o.head):
            raise Fail(f"the branch head is {git('rev-parse', '--short', br)}, not {o.head}: the group pushed again; review the new head")
        dirty = git("status", "--porcelain", "--", *kinds)
        if dirty:
            raise Fail(f"local changes on the delivery's files, resolve first: {' | '.join(dirty.splitlines())}")
        tree = Tree()
        book = {"group": group, "item": item}
        try:
            # --drop-nodes a,b (16:36 UTC): a delivered NEW node the reviewer found duplicate/unneeded is not merged; the
            # reviewer's --apply-fixes must have removed every citation of it (check_dag refuses a dangling citation)
            for nid in [x.strip() for x in (o.drop_nodes or "").split(",") if x.strip()]:
                hits = [f for f, k in kinds.items() if k == "new" and pathlib.Path(f).stem == nid]
                if not hits or exists_at("HEAD", hits[0]):
                    raise Fail(f"--drop-nodes {nid}: not a new node of this delivery")
                del kinds[hits[0]]
            merge_files(group, item, base, kinds, tree)
            nfix, nadded = apply_fixes(o.apply_fixes, kinds, tree, item, group) if o.apply_fixes else (0, 0)
            item_path = next(f for f, k in kinds.items() if k == "item")
            ids = {pathlib.Path(f).stem for f, k in kinds.items() if k in ("item", "new")}
            backfill_blueprint(ids)
            # tool uses declared by the worker in split_report.tool_uses ([{node, why}]) are copied into tool_uses at merge
            # (decision of the human, 2026-10-10 evening); --drop-tool-uses a,b leaves out the ones the reviewer rejected
            declared = []
            try:
                dd = json.loads((ROOT / item_path).read_text())
                declared = [t.get("node") for t in ((dd.get("split_report") or {}).get("tool_uses") or []) if isinstance(t, dict) and t.get("node")]
            except Exception:  # noqa: BLE001
                declared = []
            drop = [x.strip() for x in (o.drop_tool_uses or "").split(",") if x.strip()]
            declared = [x for x in declared if x not in drop and node_path(x)]
            if o.tool_uses or declared:
                tu = [x.strip() for x in (o.tool_uses or "").split(",") if x.strip()] + [x for x in declared]
                missing = [x for x in tu if not node_path(x)]
                if missing:
                    raise Fail(f"--tool-uses: no node {', '.join(missing)}")

                def add_tu(d):
                    cur = list(d.get("tool_uses") or [])
                    d["tool_uses"] = cur + [x for x in tu if x not in cur]
                edit_json(tree, item_path, add_tu)
            pre_rule = subprocess.run(["git", "merge-base", "--is-ancestor", BLUEPRINT_RULE, base], cwd=ROOT, capture_output=True).returncode != 0
            rs = subprocess.run([sys.executable, "tools/review_split.py", item], cwd=ROOT, text=True, capture_output=True)
            fails = [l.strip() for l in rs.stdout.splitlines()[1:] if l.startswith("  ")]
            if rs.returncode != 0 or "FAIL" in rs.stdout:
                if not (pre_rule and fails and all(l.startswith("blueprint:") for l in fails)):
                    raise Fail("review_split.py: " + " | ".join(l.strip() for l in (rs.stdout + rs.stderr).splitlines() if l.strip()))
            else:
                pre_rule = False
            cd = subprocess.run([sys.executable, "tools/check_dag.py"], cwd=ROOT, text=True, capture_output=True)
            # "reach:" warnings are not errors of the delivery (new nodes of other workers in progress are unreached until
            # their item is written); check_dag.py exits 1 on them, so only the listed kinds fail the merge.
            # A "route:" warning counts only when it names a delivered node (standing ones are the lead's).
            bad = [l for l in (cd.stdout + cd.stderr).splitlines()
                   if l.startswith(("error", "unit", "cycle", "deps")) or "ERROR" in l
                   or (l.startswith("route") and any(i in l for i in ids))]
            if bad:
                raise Fail("check_dag.py: " + " | ".join(bad))

            rid = o.reviewer
            verdict = (o.verdict or ("FIX" if o.apply_fixes else "PASS")).upper()
            if nadded:
                verdict = f"FIX+NODE({nadded})"   # the reviewer added statement node(s): counted separately as "merged with reviewer fix"

            def mark(d):
                note = o.reviewed or (
                    "mechanical checks by tools/merge_delivery.py; mathematics reviewed in full by " + rid + " (reviewer sub-agent of L)"
                    + (f"; spot-checked: {o.spot_checked}" if o.spot_checked else "")
                    + (f"; {nfix} file(s) fixed by the reviewer" if nfix else "")
                    + (f"; {nadded} statement node(s) added by the reviewer (FIX more, RETURN less)" if nadded else "")
                    + ("; delivered before the blueprint-refs rule: blueprint field backfilled by tools/blueprint_refs.py, same_as not yet searched" if pre_rule else ""))
                d["reviewed"] = {"date": today(), "by": "L", "reviewer": rid, "group": group, "result": "pass", "note": note}
                if o.lead_note:
                    add = f"{today()} L ({rid}): {o.lead_note}"
                    d["lead_note"] = (d["lead_note"].rstrip() + " " + add) if isinstance(d.get("lead_note"), str) and d["lead_note"].strip() else add
            edit_json(tree, item_path, mark)

            # bookkeeping: the return entry, the claim, the ledger line
            rp, rtext, parts = return_entries(group, item)
            keep = [x for x in parts if not x.startswith(f"## {item} (")]
            returned = rtext is not None and len(keep) != len(parts)
            book["returns"] = (rp, rtext)
            if returned:
                rp.write_text("".join(keep))
            claim = ROOT / "coord" / "claims" / (item.replace("/", "__") + ".lock")
            book["claim"] = (claim, claim.read_text() if claim.exists() else None)
            dlog = ROOT / "coord" / "deliveries.log"
            book["dlog"] = (dlog, dlog.read_text() if dlog.exists() else "")
            done = subprocess.run([sys.executable, "tools/claim.py", "done", group, item,
                                   f"delivered by {group} on {br}, merged by L (reviewer {rid})"],
                                  cwd=ROOT, text=True, capture_output=True)
            new = [f for f, k in kinds.items() if k == "new"]
            book["ledger"] = ledger_line(
                f"merged {br} (reviewer {verdict}; {'after a return' if returned else 'first push'}; new nodes: {len(new)})"
                + ("" if done.stdout.startswith("done") else f"; claim not held by {group}: {done.stdout.strip()}"))

            author = git("show", "-s", "--format=%an <%ae>", commits[-1])
            paths = list(kinds) + ["coord/ledger.md", "coord/deliveries.log"]
            if returned:
                paths.append(rp.relative_to(ROOT).as_posix())
            if book["claim"][1] is not None and exists_at("HEAD", claim.relative_to(ROOT).as_posix()):
                paths.append(claim.relative_to(ROOT).as_posix())
            git_retry("add", "-A", "--", *paths)
            git_retry("commit", "-q", f"--author={author}", "-m",
                      f"Split {item} ({group}, reviewed by {rid})\n\nDelivered by group {group} ({br}, {git('rev-parse', '--short', br)}); "
                      f"reviewer {rid}: {verdict}; merged by tools/merge_delivery.py for L.", "--", *paths)
        except BaseException:
            tree.restore()
            unbook(book)
            raise
        sha = git("rev-parse", "--short", "HEAD")
        git("branch", "-D", br, check=False)
        refresh_queue(item)
    print(f"MERGED {item} {sha}")
    return 0


def unbook(book):
    """Undo the bookkeeping of a merge that did not commit."""
    if "ledger" in book:
        remove_line(ROOT / "coord" / "ledger.md", book["ledger"])
    if "returns" in book:
        p, t = book["returns"]
        if t is not None:
            p.write_text(t)
    if "claim" in book:
        p, t = book["claim"]
        if t is not None and not p.exists():
            p.write_text(t)
    if "dlog" in book:
        p, before = book["dlog"]
        if p.exists():
            now = p.read_text()
            if now.startswith(before):
                added = [l for l in now[len(before):].splitlines(True) if f" {book['group']} done {book['item']} " not in l]
                p.write_text(before + "".join(added))
        subprocess.run(["git", "reset", "-q", "--", "coord/deliveries.log", "coord/ledger.md"], cwd=ROOT, capture_output=True)


def refresh_queue(item):
    """The queue after the merge, unless it was written less than 60 s ago (a merge right before)."""
    q = ROOT / "coord" / "queue.tsv"
    if q.exists() and time.time() - q.stat().st_mtime < 60:
        return
    subprocess.run([sys.executable, "tools/blueprint_refs.py", "backfill"], cwd=ROOT, capture_output=True)
    r = subprocess.run([sys.executable, "tools/queue.py", "write"], cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        return
    paths = ["coord/queue.tsv", "coord/queue.md", "coord/blueprint-index.tsv"]
    if not git("status", "--porcelain", "--", *paths):
        return
    try:
        git_retry("add", "--", *paths)
        git_retry("commit", "-q", "-m", f"Queue after the merge of {item}", "--", *paths)
    except Fail:
        pass  # the queue is rewritten by the next merge or by the lead


def cmd_return(group, item, reasons):
    if not reasons.strip():
        raise Fail("no reasons given")
    if git("symbolic-ref", "-q", "--short", "HEAD", check=False) != MAIN:
        raise Fail(f"the working tree is not on {MAIN}")
    br = branch_of(group, item)
    with merge_lock():
        head = git("rev-parse", "--short", f"refs/heads/{br}") if has_ref(f"refs/heads/{br}") else "no branch"
        p, before, parts = return_entries(group, item)
        rel = p.relative_to(ROOT).as_posix()
        line = None
        try:
            p.parent.mkdir(exist_ok=True)
            # keep the returns file exact: one entry per item, the latest
            kept = [x for x in parts if not x.startswith(f"## {item} (")]
            text = "".join(kept).rstrip("\n") + "\n" if kept else ""
            text += f"\n## {item} ({datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%d %H:%M')} UTC, branch head {head})\n\n{reasons.strip()}\n"
            p.write_text(text)
            short = " ".join(reasons.split())[:120]
            line = ledger_line(f"returned {br} (reviewer RETURN: {short})")
            git_retry("add", "--", rel, "coord/ledger.md")
            git_retry("commit", "-q", "-m", f"return to {group}: {item}", "--", rel, "coord/ledger.md")
        except BaseException:
            if before is None:
                p.unlink(missing_ok=True)
            else:
                p.write_text(before)
            if line:
                remove_line(ROOT / "coord" / "ledger.md", line)
            subprocess.run(["git", "reset", "-q", "--", rel, "coord/ledger.md"], cwd=ROOT, capture_output=True)
            raise
        sha = git("rev-parse", "--short", "HEAD")
    print(f"RETURNED {item} {sha}")
    return 0


# ---------------------------------------------------------------- stage 2

def cmd_merge2(o):
    """A stage-2 delivery: land the modules in dependency order, record `lean` and `reviewed_lean` on the item, on the
    new definition nodes (written whole, with `reviewed`) and on the dependency nodes, the item's added stmt_deps, the
    report, the bookkeeping (coord/STATE.md, STAGE 2 EXTRA NODES)."""
    import stage2_delivery as s2
    group, item = o.group, o.item
    br = branch_of(group, item)
    dry = o.dry_run
    say = (lambda m: print(f"  would {m}")) if dry else (lambda m: None)
    if not o.head:
        raise Fail("--stage 2 needs --head SHA (the commit the reviewer read)")
    if git("symbolic-ref", "-q", "--short", "HEAD", check=False) != MAIN:
        raise Fail(f"the working tree is not on {MAIN}")
    lock = merge_lock()  # a dry run too: it reads the tree a merge may be writing
    with lock:
        # (1) the branch and its head
        if not has_ref(f"refs/heads/{br}"):
            raise Fail(f"no branch {br}")
        if not git("rev-parse", br).startswith(o.head):
            raise Fail(f"the branch head is {git('rev-parse', '--short', br)}, not {o.head}: the group pushed again; review the new head")
        base = git("merge-base", MAIN, br)
        age = time.time() - int(git("show", "-s", "--format=%ct", base))
        if age > MAX_AGE:
            raise Fail(f"base {base[:7]} is {age/3600:.0f} h behind {MAIN}: pull {MAIN}, rebase, push again")
        G = s2.Git(ROOT)
        drop = [x.strip() for x in (o.drop_nodes or "").split(",") if x.strip()]
        D = s2.read_delivery(G, br, base, group, item, drop=drop)
        nfix, fixnotes = 0, []
        if o.apply_fixes:
            # DIR: <basename>.lean for any module of the delivery, <item>.lean-record.json (the item's record),
            # <new node id>.json (a new node file, replaced whole), <item>.report.md. The delivery is then read and
            # checked again on the fixed versions.
            fixdir = pathlib.Path(o.apply_fixes).resolve()
            if not fixdir.is_dir():
                raise Fail(f"--apply-fixes {fixdir}: no such directory")
            bybase = {}
            for m in D["modules"]:
                bybase.setdefault(pathlib.PurePosixPath(m["file"]).name, []).append(m)
            rec_name, rep_name = f"{item}.lean-record.json", f"{item}.report.md"
            sc_name = f"{item}.statement-change.json"
            texts, override, nodefix, overrides, scfix = {}, None, {}, {}, None
            for p in sorted(x for x in fixdir.rglob("*") if x.is_file()):
                r = p.relative_to(fixdir).as_posix()
                if r in bybase:
                    if len(bybase[r]) > 1:
                        raise Fail(f"--apply-fixes: {r}: several modules of the delivery have this basename")
                    texts[bybase[r][0]["file"]] = p.read_text()
                elif r == sc_name:
                    try:
                        scfix = json.loads(p.read_text())
                    except ValueError as e:
                        raise Fail(f"--apply-fixes: {r}: not valid JSON ({e})")
                    if not isinstance(scfix, dict):
                        raise Fail(f"--apply-fixes: {r}: not a JSON object")
                elif r == rec_name or (r.endswith(".json") and r[:-5] in D["new"]):
                    try:
                        x = json.loads(p.read_text())
                    except ValueError as e:
                        raise Fail(f"--apply-fixes: {r}: not valid JSON ({e})")
                    if not isinstance(x, dict):
                        raise Fail(f"--apply-fixes: {r}: not a JSON object")
                    if r == rec_name:
                        override = x
                    else:
                        nodefix[r[:-5]] = x
                elif r == rep_name:
                    overrides[D["report_path"]] = p.read_text()
                else:
                    raise Fail(f"--apply-fixes: {r}: a stage-2 fix is only DIR/<basename of a module>.lean "
                               f"({', '.join(sorted(bybase)) or 'no module'}), DIR/{rec_name}, DIR/{sc_name}, DIR/<new node id>.json "
                               f"({', '.join(D['new']) or 'no new node'}) or DIR/{rep_name}")
                nfix += 1
            # the node files with their refitted records
            nodes = {item: (D["node_path"], json.loads(json.dumps(D["node"])))}
            for nid, x in D["new"].items():
                nodes[nid] = (x["path"], nodefix.get(nid) or json.loads(json.dumps(x["node"])))
            for nid, x in D["deps"].items():
                nodes[nid] = (x["path"], json.loads(json.dumps(x["node"])))
            for nid in nodefix:
                overrides[nodes[nid][0]] = dump(nodes[nid][1])
            if scfix is not None:
                # the reviewer's statement_change replaces the delivered one (checked again by read_delivery)
                nodes[item][1]["statement_change"] = scfix
                overrides[nodes[item][0]] = dump(nodes[item][1])
            for nid, (path, nd) in nodes.items():
                rec = nd.get("lean")
                if not isinstance(rec, dict):
                    continue
                f = rec.get("file")
                fixed = f in texts
                ov = override if nid == item else None
                if not fixed and ov is None:
                    continue
                text = texts.get(f) if fixed else (G.show(br, f) if f else None)
                newrec, notes, refuse = s2.refit_record(text, rec, ov, o.reviewer, fixed)
                if refuse:
                    raise Fail(f"stage-2 fix of {nid}: " + " | ".join(refuse))
                fixnotes += [f"{nid}: {x}" for x in notes]
                if newrec != rec:
                    nd["lean"] = newrec
                    overrides[path] = dump(nd)
            for fpath, text in texts.items():
                overrides[fpath] = text
            D = s2.read_delivery(G, br, base, group, item, overrides=overrides, drop=drop)
        fails = list(D["fails"])
        if fails:
            raise Fail("stage-2 checks: " + " | ".join(f"({L}) {x}" for L, x in fails))
        if not isinstance(D["rec"], dict):
            raise Fail("the node has no `lean` record")
        node_rel = node_path(item)
        if node_rel is None or node_rel != D["node_path"]:
            raise Fail(f"the node file of {item} is {node_rel} on {MAIN}, {D['node_path']} on the branch")
        new, deps, mods = D["new"], D["deps"], D["modules"]
        for nid, x in new.items():
            if node_path(nid) is not None or exists_at("HEAD", x["path"]):
                raise Fail(f"the new node {nid} exists on {MAIN} now (another delivery created it): return the delivery")
        if D.get("corrected"):
            curi = json.loads((ROOT / node_rel).read_text())
            moved = [k for k in STAGE2_ITEM_CORRECTION if curi.get(k) != D["base_node"].get(k)]
            if moved:
                raise Fail(f"the item is corrected by the delivery but its {', '.join(moved)} changed on {MAIN} since the "
                           "delivery's base: the reviewer decides and the group re-pushes")
        for nid, x in deps.items():
            if node_path(nid) != x["path"]:
                raise Fail(f"the dependency node {nid} is not {x['path']} on {MAIN}")
            cur = json.loads((ROOT / x["path"]).read_text())
            if cur.get("lean") != x["base_node"].get("lean"):
                raise Fail(f"the dependency node {nid}: its `lean` changed on {MAIN} since the delivery's base "
                           f"({json.dumps(cur.get('lean'), ensure_ascii=False)[:200]}); the reviewer decides and the group re-pushes")
        # the records: statement re-read from each module (refreshed after its landing)
        records = {}
        for nid, rec in [(item, D["rec"])] + [(k, v["node"].get("lean")) for k, v in new.items()] + [(k, v["node"].get("lean")) for k, v in deps.items()]:
            records[nid] = dict(rec)
        for m in mods:
            if m["decl"] is not None:
                records[m["node"]]["statement"] = m["decl"]["statement"]
        report = D["report"]
        report_rel = D["report_path"]
        if dry:
            print(f"DRY RUN {item} (stage 2): branch {br} at {git('rev-parse', '--short', br)}, base {base[:9]}; checks (a)-(e) pass"
                  + (f"; {nfix} file(s) fixed by the reviewer" if nfix else ""))
            for r in D.get("roles") or []:
                print(f"  delivery: {r}")
            for n in D["notes"] + fixnotes:
                print(f"  note: {n}")
        rid = o.reviewer
        verdict = (o.verdict or ("FIX" if nfix else "PASS")).upper()
        reviewed = {"date": today(), "by": "L", "reviewer": rid, "group": group, "result": verdict.lower()}
        dropped = list(D.get("dropped") or {})
        dnote = (f"dropped duplicate new node(s) {', '.join(dropped)} (--drop-nodes; not merged, the item points at the "
                 "landed declaration)") if dropped else ""
        if o.spot_checked or dnote:
            reviewed["note"] = "; ".join(x for x in (o.spot_checked, dnote) if x)
        reviewed_new = {"date": today(), "by": "L", "reviewer": rid, "group": group, "result": verdict.lower(),
                        "note": "new definition node of a stage-2 delivery, read against its source by the reviewer"}
        tree = Tree()
        book = {"group": group, "item": item}
        landed = []   # (module, landing id)
        paths_nodes = {item: node_rel}
        docs = {}

        def put(nid):
            say(f"set {paths_nodes[nid]}: lean = {json.dumps(docs[nid].get('lean'), ensure_ascii=False)}")
            if not dry:
                tree.write(paths_nodes[nid], dump(docs[nid]))
        try:
            # (3) the nodes: `lean` and `reviewed_lean` on the current version of the item and of each dependency node;
            # the new nodes written whole with `reviewed` and `reviewed_lean`; the item's stmt_deps gain the new nodes
            cur = json.loads((ROOT / node_rel).read_text())
            cur["lean"] = records[item]
            cur["reviewed_lean"] = dict(reviewed, statement_corrected=True) if D.get("corrected") else reviewed
            if D.get("corrected"):
                # STAGE 2 STATEMENT CORRECTION: the corrected fields from the delivered node (checked against the base
                # by node_fields.check_statement_change; unchanged on MAIN since the base, checked above)
                for k in STAGE2_ITEM_CORRECTION:
                    if k in D["node"]:
                        cur[k] = D["node"][k]
                    else:
                        cur.pop(k, None)
                say(f"set {node_rel}: the corrected statement, stmt_deps, proof, proof_deps and statement_change "
                    f"({len(D.get('citers') or [])} citer(s), "
                    f"{sum(1 for c in D.get('citer_marks') or [] if c.get('holds') is False)} marked holds:false)")
            elif D.get("added_deps"):
                sd = list(cur.get("stmt_deps") or [])
                cur["stmt_deps"] = sd + [x for x in D["added_deps"] if x not in sd]
                say(f"set {node_rel}: stmt_deps = {cur['stmt_deps']} (added {D['added_deps']})")
            docs[item] = cur
            say(f"set {node_rel}: reviewed_lean = {json.dumps(cur['reviewed_lean'], ensure_ascii=False)}")
            put(item)
            for nid, x in new.items():
                nd = dict(x["node"])
                nd["lean"] = records[nid]
                nd["reviewed"] = reviewed_new
                nd["reviewed_lean"] = reviewed
                docs[nid] = nd; paths_nodes[nid] = x["path"]
                say(f"write the new node {x['path']} with reviewed = {json.dumps(reviewed_new, ensure_ascii=False)} and reviewed_lean")
                put(nid)
            for nid, x in deps.items():
                nd = json.loads((ROOT / x["path"]).read_text())
                nd["lean"] = records[nid]
                nd["reviewed_lean"] = reviewed
                docs[nid] = nd; paths_nodes[nid] = x["path"]
                say(f"set the dependency node {x['path']}: lean (mathlib_match kept) and reviewed_lean")
                put(nid)
            # (4) the report
            say(f"write {report_rel} ({len(report or '')} characters) "
                + ("from the reviewer's fix" if nfix and report != G.show(br, report_rel) else "from the branch"))
            if not dry:
                tree.write(report_rel, report)
            # (2) the landings, in dependency order, last before the bookkeeping. With several modules, every module
            # that imports no sibling is compiled first in lean/.sandbox/L/, so that a failure aborts before any landing.
            if len(mods) > 1:
                say(f"compile first, in lean/.sandbox/L/: {', '.join(m['file'] for m in mods if not m['siblings'])}")
                if not dry:
                    for c in s2.compile_modules(D, "L", ROOT):
                        if c["status"] == "fail":
                            raise Fail(f"{c['file']} ({c['node']}) does not compile; nothing landed: "
                                       + " | ".join(c["out"].splitlines()[-25:]))
            for m in mods:
                lib_rel = m["file"]
                sand = ROOT / "lean" / ".sandbox" / "L" / f"{m['node']}.lean"
                cmd = ["bash", str(ROOT / "tools" / "land.sh"), str(sand), str(ROOT / lib_rel)]
                say(f"write {sand.relative_to(ROOT)} ({len(m['text'].splitlines())} lines) and run SHEAF_GROUP=L tools/land.sh "
                    f"{sand.relative_to(ROOT)} {lib_rel}  [{m['role']} {m['node']}]")
                if dry:
                    continue
                sand.parent.mkdir(parents=True, exist_ok=True)
                sand.write_text(m["text"])
                r = subprocess.run(cmd, cwd=ROOT, env=dict(_os.environ, SHEAF_GROUP="L"), text=True, capture_output=True)
                if r.returncode != 0:
                    raise Fail(f"land.sh {lib_rel} exit {r.returncode}: " + " | ".join((r.stdout + r.stderr).strip().splitlines()[-25:]))
                mm = re.search(r"as landing (\S+)", r.stdout)
                landed.append((m["module"], mm.group(1) if mm else (r.stdout.strip().splitlines() or ["?"])[-1]))
                rec = records[m["node"]]
                got = next((d for d in s2.declarations((ROOT / lib_rel).read_text()) if d["name"] == rec["declaration"]), None)
                if got is None:
                    raise Fail(f"{rec['declaration']} not found in the landed {lib_rel}")
                if got["statement"] != rec["statement"]:
                    rec["statement"] = got["statement"]; docs[m["node"]]["lean"] = rec
                    tree.write(paths_nodes[m["node"]], dump(docs[m["node"]]))
            # (5) bookkeeping as in stage 1: the return entry, the claim, the ledger line, the commit
            rp, rtext, parts = return_entries(group, item)
            keep = [x for x in parts if not x.startswith(f"## {item} (")]
            returned = rtext is not None and len(keep) != len(parts)
            claim = ROOT / "coord" / "claims" / (item.replace("/", "__") + ".lock")
            rec = records[item]
            extra = (f"; new nodes: {', '.join(new)}" if new else "") + (f"; dropped nodes: {', '.join(dropped)}" if dropped else "") + (f"; dependency modules: {', '.join(deps)}" if deps else "") \
                + (f"; statement corrected ({len(D.get('citers') or [])} citers)" if D.get("corrected") else "")
            ltext = (f"merged {br} (stage 2; reviewer {verdict}; {'after a return' if returned else 'first push'}; "
                     f"{rec.get('module')} {rec.get('declaration')}{'; existing declaration' if rec.get('existing') else ''}{extra})")
            author = git("show", "-s", "--format=%an <%ae>", D["commits"][-1]) if D["commits"] else "L"
            paths = list(paths_nodes.values()) + [report_rel, "coord/ledger.md", "coord/deliveries.log"] + [m["file"] for m in mods]
            msg = (f"State {item} ({group}, reviewed by {rid})" + ("; statement corrected" if D.get("corrected") else "")
                   + (f"; new nodes: {', '.join(new)}" if new else "")
                   + (f"; dropped: {', '.join(dropped)}" if dropped else "")
                   + f"\n\nDelivered by group {group} ({br}, {git('rev-parse', '--short', br)}); "
                   f"reviewer {rid}: {verdict}; merged by tools/merge_delivery.py --stage 2 for L."
                   + (("\nDependency modules: " + ", ".join(f"{k} ({records[k].get('module')})" for k in deps) + ".") if deps else ""))
            if dry:
                if returned:
                    print(f"  would drop the return entry of {item} from {rp.relative_to(ROOT)}")
                print(f"  would run tools/claim.py done {group} {item} (claim file {'present' if claim.exists() else 'absent'})")
                print(f"  would append the ledger line: - HH:MM L: {ltext}")
                print(f"  would commit {paths + ([rp.relative_to(ROOT).as_posix()] if returned else [])} as {author}:")
                print("    " + msg.replace("\n", "\n    "))
                print(f"  would delete the branch {br} and rewrite the queue (if coord/queue.tsv is older than 60 s)")
                print(f"DRY RUN {item}: nothing changed")
                return 0
            book["returns"] = (rp, rtext)
            if returned:
                rp.write_text("".join(keep))
            book["claim"] = (claim, claim.read_text() if claim.exists() else None)
            dlog = ROOT / "coord" / "deliveries.log"
            book["dlog"] = (dlog, dlog.read_text() if dlog.exists() else "")
            done = subprocess.run([sys.executable, "tools/claim.py", "done", group, item,
                                   f"delivered by {group} on {br}, merged by L (reviewer {rid})"],
                                  cwd=ROOT, text=True, capture_output=True)
            book["ledger"] = ledger_line(ltext + ("" if done.stdout.startswith("done") else f"; claim not held by {group}: {done.stdout.strip()}"))
            if returned:
                paths.append(rp.relative_to(ROOT).as_posix())
            if book["claim"][1] is not None and exists_at("HEAD", claim.relative_to(ROOT).as_posix()):
                paths.append(claim.relative_to(ROOT).as_posix())
            git_retry("add", "-A", "--", *paths)
            git_retry("commit", "-q", f"--author={author}", "-m", msg, "--", *paths)
        except BaseException as e:
            tree.restore()
            unbook(book)
            if landed and isinstance(e, Fail):
                raise Fail(f"{e}. STOPPED AFTER PARTIAL LANDING, NOTHING COMMITTED: landed {', '.join(f'{m} as landing {i}' for m, i in landed)}; "
                           f"revert each with `tools/landing.py revert <id> <reason>` "
                           f"({'; '.join(f'tools/landing.py revert {i} merge of {item} failed' for _, i in landed)}) before merging again")
            raise
        sha = git("rev-parse", "--short", "HEAD")
        git("branch", "-D", br, check=False)
        refresh_queue(item)
    print(f"MERGED {item} {sha}" + (f" (new nodes: {', '.join(new)})" if new else ""))
    return 0


def main():
    a = sys.argv[1:]
    if not a or a[0] in ("-h", "--help"):
        print(__doc__); return 0
    if a[0] == "list":
        try:
            return cmd_list()
        except Fail as e:
            print(e); return 1
    if a[0] == "show":
        try:
            return cmd_show(a[1], a[2])
        except Fail as e:
            print(f"NOT MERGED {a[2]}: {e}"); return 1
    if a[0] == "return":
        if len(a) < 4:
            print("usage: merge_delivery.py return <group> <item> REASONS"); return 2
        try:
            return cmd_return(a[1], a[2], " ".join(a[3:]))
        except Exception as e:  # noqa: BLE001
            print(f"NOT RETURNED {a[2]}: {e}"); return 1
    ap = argparse.ArgumentParser(prog="merge_delivery.py", add_help=False)
    ap.add_argument("group"); ap.add_argument("item")
    ap.add_argument("--spot-checked"); ap.add_argument("--reviewer", default="reviewer")
    ap.add_argument("--apply-fixes"); ap.add_argument("--tool-uses"); ap.add_argument("--drop-tool-uses"); ap.add_argument("--drop-nodes"); ap.add_argument("--reviewed")
    ap.add_argument("--lead-note"); ap.add_argument("--verdict", choices=["PASS", "FIX", "pass", "fix"])
    ap.add_argument("--head")
    ap.add_argument("--stage", choices=["1", "2"], default="1"); ap.add_argument("--dry-run", action="store_true")
    try:
        o = ap.parse_args(a)
    except SystemExit:
        print(f"NOT MERGED {a[1] if len(a) > 1 else '?'}: bad arguments (see --help)"); return 1
    if o.dry_run and o.stage != "2":
        print(f"NOT MERGED {o.item}: --dry-run is for --stage 2 only"); return 1
    try:
        return cmd_merge2(o) if o.stage == "2" else cmd_merge(o)
    except Exception as e:  # noqa: BLE001
        print(f"NOT MERGED {o.item}: {e}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
