#!/usr/bin/env python3
"""Batch landing of reviewed stage-1 deliveries (2026-10-16, the human: "落地需要并行").

stdin: a JSON list of approved verdicts {g, item, head, verdict PASS|FIX, note, fixes, drop_nodes}
stdout: progress lines, then one line `RESULTS_JSON {head: {rc, stdout, stderr}}`; each entry carries the same
lines tools/nt_land.py prints for that delivery (SUPERSEDED / HEAD MOVED / NOT MERGED <item>: <reason> /
MERGED <item> <sha> / PROMOTED ...), so the reviewer loop reads it exactly as before.

One chunk of up to NT_BATCH_SIZE (10) deliveries per hold of coord/.merge.lock:
  1. per delivery, the checks of tools/merge_delivery.py cmd_merge (stage-1-open, inspect, head, local changes),
     the merge by files, the reviewer's fixes, --drop-nodes, tool_uses; a delivery whose files (or fix files)
     another delivery of the round already wrote waits for the next round (no result);
  2. on the combined tree: the blueprint backfill, the cited-statement check (against the combined version of
     each cited node), tools/review_split.py (all items in one run), tools/check_dag.py --cycles against the
     cached HEAD baseline (tools/dag_delta.py, same policy as a single landing). A finding that names the nodes
     of some deliveries refuses those (NOT MERGED check_dag.py: <lines>); a finding that names none is recorded;
  3. per delivery, in order: `reviewed`, return entry, claim, ledger line, one commit `Split <item> ...` with the
     delivery's author, branch deleted. The queue refresh is requested once.
One DAG (2026-10-18, tools/livedag.py): dag/nodes is the link to the live DAG and the merge lock also holds live's lock,
so the merge writes the live node files directly and each delivery's DAG files are committed in the live repository
(merge_delivery.git) next to its side commit of the bookkeeping. promote() is a no-op for such commits; it only merges
an old journalled side commit (local/stage1-batch/pending/) field-wise into live. Lock hold times:
local/stage1-batch/locks.tsv.

No serial landing (the human, 2026-10-17 02:40): every row is decided in the round. Merged; or not stage-1-open:
retired at once (tools/retire_stage1.py, outside the chunk lock) or NOT MERGED (the reviewer loop returns it); or a
file conflict with an earlier delivery of the round (Defer): no result, the row stays queued for the next round's
batch; or cited statement changed / review_split.py / a check_dag finding naming it: NOT MERGED with the reason (the
reviewer loop writes the returns, in parallel). A chunk-wide failure (backfill, commit, unexpected error) gives the
rows left no result: they stay queued for the next round. Only a RETURN verdict row still runs tools/nt_land.py
(a return, not a landing).
"""
import contextlib
import io
import json
import os
import pathlib
import re
import subprocess
import sys
import threading
import time
import traceback

P = pathlib.Path(__file__).resolve().parent.parent
os.chdir(P)
os.environ.update(SHEAF_LEAD="L-only", SHEAF_DAG="dag/nodes")
os.environ.setdefault("SHEAF_LOCK_TIMEOUT", "300")
# fastland: one live_closed cache for this process and its check_dag runs (the HEAD baseline runs in a temporary copy)
os.environ.setdefault("SHEAF_LIVE_CLOSED_CACHE", str(P / "local" / "stage2" / "live-closed.json"))
sys.path.insert(0, str(P / "tools"))
import merge_delivery as md  # noqa: E402
import dag_queue  # noqa: E402
import dag_delta  # noqa: E402
from mergelock import merge_lock  # noqa: E402
from retire_stage1 import retire_completed  # noqa: E402
from node_fields import SPLIT_OWNS  # noqa: E402

LIVE = pathlib.Path(os.environ.get("NT_LIVE_ROOT") or P.parent / "weil-conjectures-sheaf")   # override: tests on clones only
BL = P / "local" / "stage1-batch"
PENDING = BL / "pending"
SIZE = int(os.environ.get("NT_BATCH_SIZE", "1000"))   # launcher, 2026-10-17 (the human): no per-batch limit


class Defer(Exception):
    pass


def res(rc, out, err=""):
    return {"rc": rc, "stdout": out, "stderr": err}


def say(*a):
    print(time.strftime("%T"), *a, flush=True)


def precheck(row):
    """tools/nt_land.py before merge_delivery.py: superseded or moved heads are answered here."""
    g, item, head = row["g"], row["item"], row["head"]
    try:
        r = subprocess.run(["git", "rev-parse", "--verify", "deliver/" + g + "/" + item], cwd=P, capture_output=True, text=True)
        if r.returncode and retire_completed(g, item, head):
            return res(0, f"SUPERSEDED {item} delivery already archived\n")
        if r.returncode or r.stdout.strip() != head:
            return res(1, f"HEAD MOVED/SUPERSEDED {item}\n")
        # fastland 2026-10-17: a completed (unfolded/merged) item is not stage-1-open, so land_chunk puts it in `notopen`
        # and main() retires it after the hold with this same answer; calling retire_completed here cost ~8 s a round
    except Exception:  # noqa: BLE001
        return res(1, "", traceback.format_exc())
    return None


def single(row):
    """The unchanged one-delivery path."""
    args = [sys.executable, "tools/nt_land.py", row["g"], row["item"], row["head"], row["verdict"], row["note"],
            row.get("fixes") or "-", row.get("drop_nodes") or ""]
    r = subprocess.run(args, cwd=P, capture_output=True, text=True)
    return res(r.returncode, r.stdout, r.stderr)


def prepare(row, s1, written):
    g, item, head = row["g"], row["item"], row["head"]
    br = md.branch_of(g, item)
    base, commits, kinds = md.inspect(g, item)
    if head and not md.git("rev-parse", br).startswith(head):
        raise md.Fail(f"the branch head is {md.git('rev-parse', '--short', br)}, not {head}: the group pushed again; review the new head")
    fixdir = row.get("fixes") if row["verdict"] == "FIX" else None
    extra = set()
    if fixdir and (P / fixdir).is_dir():
        extra = {p.relative_to(P / fixdir).as_posix() for p in (P / fixdir).rglob("*") if p.is_file()}
    if (set(kinds) | extra) & set(written):
        raise Defer()
    dirty = md.git("status", "--porcelain", "--", *kinds)
    if dirty:
        raise md.Fail(f"local changes on the delivery's files, resolve first: {' | '.join(dirty.splitlines())}")
    tree = md.Tree()
    try:
        for nid in [x.strip() for x in (row.get("drop_nodes") or "").split(",") if x.strip()]:
            hits = [f for f, k in kinds.items() if k == "new" and pathlib.Path(f).stem == nid]
            if not hits or md.exists_at("HEAD", hits[0]):
                raise md.Fail(f"--drop-nodes {nid}: not a new node of this delivery")
            del kinds[hits[0]]
        md.merge_files(g, item, base, kinds, tree)
        nfix, nadded = md.apply_fixes(fixdir, kinds, tree, item, g) if fixdir else (0, 0)
        item_path = next(f for f, k in kinds.items() if k == "item")
        ids = {pathlib.Path(f).stem for f, k in kinds.items() if k in ("item", "new")}
        try:
            dd = json.loads((P / item_path).read_text())
            declared = [t.get("node") for t in ((dd.get("split_report") or {}).get("tool_uses") or []) if isinstance(t, dict) and t.get("node")]
        except Exception:  # noqa: BLE001
            declared = []
        declared = [x for x in declared if md.node_path(x)]
        if declared:
            def add_tu(d):
                cur = list(d.get("tool_uses") or [])
                d["tool_uses"] = cur + [x for x in declared if x not in cur]
            md.edit_json(tree, item_path, add_tu)
    except BaseException:
        tree.restore()
        raise
    for f in tree.touched + tree.created:
        written[f] = head
    return {"row": row, "g": g, "item": item, "head": head, "br": br, "base": base, "commits": commits, "kinds": kinds,
            "tree": tree, "ids": ids, "item_path": item_path, "nfix": nfix, "nadded": nadded, "routes": []}


def drop(D, d, written):
    d["tree"].restore()
    for f in d["tree"].touched + d["tree"].created:
        written.pop(f, None)
    D.remove(d)


def cited_check(d, written, order=None):
    """As tools/merge_delivery.py, against the tree this delivery will be committed on: HEAD plus the deliveries
    BEFORE it in the chunk (a later delivery commits after it, exactly as two serial landings; it used to count too,
    29 of 77 refusals at 02:26 named a node a later delivery of the chunk changed)."""
    br = d["br"]
    order = order or {}
    cited = set()
    for f, k in d["kinds"].items():
        if k in ("item", "new"):
            # prepare() has applied the independent reader's fixes. In particular,
            # a reviewer-added node exists only in this tree, not on the branch.
            # Check the citations of the files that will actually be committed.
            cited.update(dag_queue.deps_of(json.loads((P / f).read_text()), "all"))
    for nid in cited - d["ids"]:
        rel = md.node_path(nid)
        if rel and md.exists_at(br, rel):
            before = md.load_json_at(br, rel)
            # the combined tree: a node another delivery of the chunk changed is compared as it will be committed
            earlier = rel in written and order.get(written[rel], 1 << 30) < order.get(d["head"], -1)
            now = json.loads((P / rel).read_text()) if earlier else md.load_json_at("HEAD", rel)
            if before.get("statement") != now.get("statement"):
                raise md.Fail(f"cited node {nid}: statement changed since the reviewed delivery; rebase and revalidate the citation")


def review_split(D):
    """{item: (failed, lines)}: one run for all items; an item the run does not report is run alone."""
    items = [d["item"] for d in D]
    rs = subprocess.run([sys.executable, "tools/review_split.py", *items], cwd=P, text=True, capture_output=True)
    blocks, cur = {}, None
    for line in rs.stdout.splitlines():
        m = re.match(r"^(\S+): (PASS|FAIL)", line)
        if m and m.group(1) in items:
            cur = m.group(1); blocks[cur] = [line]
        elif cur and line.strip():
            blocks[cur].append(line)
    out = {}
    for it in items:
        if it in blocks and not (rs.returncode and all(": PASS" in b[0] for b in blocks.values())):
            b = blocks[it]
            out[it] = (": FAIL" in b[0] or any(l.startswith("  ") for l in b[1:]), b)
        else:
            r = subprocess.run([sys.executable, "tools/review_split.py", it], cwd=P, text=True, capture_output=True)
            lines = [l for l in (r.stdout + r.stderr).splitlines() if l.strip()]
            out[it] = (bool(r.returncode) or "FAIL" in r.stdout, lines)
    return out


def commit_one(d):
    _t = [time.time()]; _pr = d.setdefault("prof", [])
    def tick(name):
        now = time.time(); _pr.append(f"{name} {now - _t[0]:.2f}"); _t[0] = now
    g, item, row = d["g"], d["item"], d["row"]
    rid = row.get("reviewer") or "NT-Codex-" + g + "-" + d["head"][:9]   # a row may name its reviewer (cc review service, 2026-10-17)
    verdict = row["verdict"]
    if d["nadded"]:
        verdict = f"FIX+NODE({d['nadded']})"
    nfix, nadded, pre_rule, tree, br = d["nfix"], d["nadded"], d["pre_rule"], d["tree"], d["br"]

    def mark(x):
        note = ("mechanical checks by tools/merge_delivery.py; mathematics reviewed in full by " + rid + " (reviewer sub-agent of L)"
                + (f"; spot-checked: {row['note']}" if row["note"] else "")
                + (f"; {nfix} file(s) fixed by the reviewer" if nfix else "")
                + (f"; {nadded} statement node(s) added by the reviewer (FIX more, RETURN less)" if nadded else "")
                + ("; delivered before the blueprint-refs rule: blueprint field backfilled by tools/blueprint_refs.py, same_as not yet searched" if pre_rule else ""))
        x["reviewed"] = {"date": md.today(), "by": "L", "reviewer": rid, "group": g, "result": "pass", "note": note}
    book = {"group": g, "item": item}
    d["book"] = book
    md.edit_json(tree, d["item_path"], mark)
    tick("mark")
    rp, rtext, parts = md.return_entries(g, item)
    keep = [x for x in parts if not x.startswith(f"## {item} (")]
    returned = rtext is not None and len(keep) != len(parts)
    book["returns"] = (rp, rtext)
    if returned:
        rp.write_text("".join(keep))
    claim = P / "coord" / "claims" / (item.replace("/", "__") + ".lock")
    book["claim"] = (claim, claim.read_text() if claim.exists() else None)
    dlog = P / "coord" / "deliveries.log"
    book["dlog"] = (dlog, dlog.read_text() if dlog.exists() else "")
    done = subprocess.run([sys.executable, "tools/claim.py", "done", g, item, f"delivered by {g} on {br}, merged by L (reviewer {rid})"],
                          cwd=P, text=True, capture_output=True)
    # 2026-10-18 (s1loop): the landing resolves a released stage-1 repair note itself; `claim.py done` resolves it only
    # for the claim holder, and 39 re-splits landed since 10-17 without it (committed with this landing below)
    _np = P / "coord" / "repair-notes" / (item + ".json")
    book["note"] = (_np, _np.read_text() if _np.exists() else None)
    dag_queue.resolve_stage1_note(item, f"{g} {d['head'][:12]} reviewed by {rid}")
    tick("claim")
    new = [f for f, k in d["kinds"].items() if k == "new"]
    book["ledger"] = md.ledger_line(
        f"merged {br} (reviewer {verdict}; {'after a return' if returned else 'first push'}; new nodes: {len(new)})"
        + ("" if done.stdout.startswith("done") else f"; claim not held by {g}: {done.stdout.strip()}"))
    author = md.git("show", "-s", "--format=%an <%ae>", d["commits"][-1])
    paths = list(d["kinds"]) + ["coord/ledger.md", "coord/deliveries.log"]
    if returned:
        paths.append(rp.relative_to(P).as_posix())
    if book["claim"][1] is not None and md.exists_at("HEAD", claim.relative_to(P).as_posix()):
        paths.append(claim.relative_to(P).as_posix())
    note = P / "coord" / "repair-notes" / (item + ".json")
    if note.exists() and md.git("status", "--porcelain", "--", note.relative_to(P).as_posix()).strip():
        paths.append(note.relative_to(P).as_posix())
    tick("prep")
    md.git_retry("add", "-A", "--", *paths)
    tick("add")
    md.git_retry("commit", "-q", f"--author={author}", "-m",
                 f"Split {item} ({g}, reviewed by {rid})\n\nDelivered by group {g} ({br}, {md.git('rev-parse', '--short', br)}); "
                 f"reviewer {rid}: {verdict}; merged by tools/nt_land_batch.py for L (batch landing).", "--", *paths)
    tick("commit")
    full = md.git("rev-parse", "HEAD")
    md.git("branch", "-D", br, check=False)
    tick("branch")
    try:
        with open(BL / "commit-prof.tsv", "a") as fh:
            fh.write(time.strftime("%F %T") + "\t" + item + "\t" + " ".join(_pr) + "\n")
    except OSError:
        pass
    return full


@contextlib.contextmanager
def _restore_on_error(state, merged):
    try:
        yield
    except BaseException:
        done = {id(d) for d, _ in merged}
        for d in state.get("D", []):
            if id(d) not in done:
                d["tree"].restore()
                if "book" in d:
                    md.unbook(d["book"])
        raise


def land_chunk(rows, results, notopen, again):
    """Lands what it can of rows under one lock hold; fills results, notopen (decided after the hold) and again
    (no result: next round)."""
    merged = []
    t0 = time.time(); tl = None; phases = {}; state = {}
    try:
        with md.merge_lock(), _restore_on_error(state, merged):
            tl = time.time()
            if md.git("symbolic-ref", "-q", "--short", "HEAD", check=False) != md.MAIN:
                raise md.Fail(f"the working tree is not on {md.MAIN}")
            s1 = {nid for _, nid in dag_queue.Dag(dag_queue.load()).stage1()}
            written, D = {}, []
            state["D"] = D
            for row in rows:
                if row["item"] not in s1:
                    notopen.append(row); continue     # retired or refused right after the hold (main)
                try:
                    D.append(prepare(row, s1, written))
                except Defer:
                    again.append(row)
                except Exception as e:  # noqa: BLE001
                    results[row["head"]] = res(1, f"NOT MERGED {row['item']}: {e}\n")
            phases["merge"] = time.time() - tl
            # baseline of HEAD (cached by tree; else computed beside the checks below)
            bres = {}
            bt = threading.Thread(target=lambda: bres.__setitem__("v", dag_delta.check_ref("HEAD")), daemon=True); bt.start()
            if D:
                try:
                    with contextlib.redirect_stdout(io.StringIO()):
                        md.backfill_blueprint(set().union(*[d["ids"] for d in D]))
                except Exception:  # noqa: BLE001
                    say("blueprint backfill failed, the chunk stays queued:", traceback.format_exc()[-400:])
                    for d in list(D):
                        drop(D, d, written); again.append(d["row"])
            order = {d["head"]: i for i, d in enumerate(D)}
            for d in list(D):
                try:
                    cited_check(d, written, order)
                except Exception as e:  # noqa: BLE001
                    results[d["head"]] = res(1, f"NOT MERGED {d['item']}: {e}\n"); drop(D, d, written)
            pre_cd, n_pre = {}, len(D)
            if D:
                ct = threading.Thread(target=lambda: pre_cd.__setitem__("v", subprocess.run(
                    [sys.executable, "tools/check_dag.py", "--cycles"], cwd=P, text=True, capture_output=True)), daemon=True)
                ct.start()
                rsr = review_split(D)
                for d in list(D):
                    failed, lines = rsr[d["item"]]
                    pre_rule = subprocess.run(["git", "merge-base", "--is-ancestor", md.BLUEPRINT_RULE, d["base"]], cwd=P, capture_output=True).returncode != 0
                    fails = [l.strip() for l in lines[1:] if l.startswith("  ")]
                    if failed:
                        if not (pre_rule and fails and all(l.startswith("blueprint:") for l in fails)):
                            results[d["head"]] = res(1, f"NOT MERGED {d['item']}: review_split.py: " + " | ".join(l.strip() for l in lines if l.strip()) + "\n")
                            drop(D, d, written); continue
                    else:
                        pre_rule = False
                    d["pre_rule"] = pre_rule
            phases["review"] = time.time() - tl - phases["merge"]
            for rnd in range(3):
                if not D:
                    break
                if rnd == 0 and len(D) == n_pre:
                    ct.join()                     # ran on this same tree beside review_split.py
                cd = pre_cd["v"] if rnd == 0 and len(D) == n_pre and "v" in pre_cd else \
                    subprocess.run([sys.executable, "tools/check_dag.py", "--cycles"], cwd=P, text=True, capture_output=True)
                bt.join()
                baseline = bres["v"] if "v" in bres else dag_delta.check_ref("HEAD")
                ids = set().union(*[d["ids"] for d in D])
                bad, routes = dag_delta.delivery_findings(cd.stdout + cd.stderr, baseline, ids)
                # launcher, 2026-10-17: a finding that names no node of the chunk (e.g. a summary/count line that differs
                # from the baseline only because the tree grew) is recorded, not blocking; it used to take the whole
                # chunk out (193 deliveries -> 0 landed, all sent to the serial path)
                unnamed = [l for l in bad if not any(dag_delta.mentions(l, d["ids"]) for d in D)]
                if unnamed:
                    say("chunk check_dag findings naming no delivery (recorded, not refused):", " | ".join(unnamed)[:600])
                bad = [l for l in bad if l not in unnamed]
                if not bad:
                    for d in D:
                        d["routes"] = [l for l in routes if dag_delta.mentions(l, d["ids"])]
                    break
                owners = [[d for d in D if dag_delta.mentions(l, d["ids"])] for l in bad]
                say("chunk check_dag findings:", " | ".join(bad)[:600])
                out = list({id(d): d for o in owners for d in o}.values())     # only the deliveries the findings name
                for d in out:                                                    # refused with the lines naming it
                    mine = [l for l in bad if dag_delta.mentions(l, d["ids"])]
                    results[d["head"]] = res(1, f"NOT MERGED {d['item']}: check_dag.py: " + " | ".join(mine) + "\n")
                    drop(D, d, written)
            phases["check"] = time.time() - tl - phases["merge"] - phases["review"]
            _tc = time.time()
            for k, d in enumerate(D):
                try:
                    full = commit_one(d)
                except Exception as e:  # noqa: BLE001
                    d["tree"].restore(); md.unbook(d.get("book", {}))
                    results[d["head"]] = res(1, f"NOT MERGED {d['item']}: {e}\n")
                    for r in D[k + 1:]:
                        r["tree"].restore(); again.append(r["row"])
                    say("commit failed, the rest of the chunk stays queued:", d["item"], str(e)[:300])
                    break
                merged.append((d, full))
                PENDING.mkdir(parents=True, exist_ok=True)
                (PENDING / (full + ".json")).write_text(json.dumps({"g": d["g"], "item": d["item"], "head": d["head"]}) + "\n")
                results[d["head"]] = res(0, "".join("check_dag.py (recorded, not refused): " + l + "\n" for l in d["routes"])
                                         + f"MERGED {d['item']} {full[:10]}\n")
            phases["commit"] = time.time() - _tc; _tc = time.time()
            if merged:
                buf = io.StringIO()
                with contextlib.redirect_stdout(buf):
                    md.refresh_queue(merged[-1][0]["item"])
                phases["refresh"] = time.time() - _tc
                h = merged[-1][0]["head"]
                results[h]["stdout"] = buf.getvalue() + results[h]["stdout"]
    except md.Fail as e:     # the lock (or the branch) refused the whole chunk: same answer as a single landing
        for row in rows:
            if row["head"] not in results and row not in notopen and row not in again:
                results[row["head"]] = res(1, f"NOT MERGED {row['item']}: {e}\n")
    except Exception:  # noqa: BLE001
        # unexpected: the uncommitted files of the chunk were put back below; what is left lands alone (the old path)
        say("chunk error, the rest stays queued for the next round:", traceback.format_exc()[-800:])
    finally:
        held = time.time() - tl if tl else 0
        BL.mkdir(parents=True, exist_ok=True)
        with open(BL / "locks.tsv", "a") as f:
            f.write(f"{time.strftime('%F %T')}\t{len(rows)}\t{len(merged)}\twait {(tl or time.time()) - t0:.1f}\thold {held:.1f}\t"
                    + " ".join(f"{k} {v:.1f}" for k, v in phases.items()) + "\n")
        say(f"chunk {len(rows)} rows: merged {len(merged)}, hold {held:.1f} s", phases)
    try:
        dag_delta.warm_head()
    except Exception:  # noqa: BLE001
        pass
    return merged


def _merge_fields(before, after, current):
    """The live node after a delivery changed `before` into `after`: every field the delivery changed is taken from
    `after`, every other field (Lean, audits, repair data, maintainer notes) stays as live has it."""
    if current is None:
        return dict(after)
    out = dict(current)
    if before is None:          # a new node of the delivery that live has too: live's record plus the split's fields
        for k, v in after.items():
            if k in SPLIT_OWNS or k not in out:
                out[k] = v
        return out
    for k in set(before) | set(after):
        if before.get(k, KeyError) != after.get(k, KeyError):
            if k in after:
                out[k] = after[k]
            else:
                out.pop(k, None)
    return out


def promote(entries):
    """entries: [(side commit, g, item, head)] -> {head: line}.

    One DAG (2026-10-18, tools/livedag.py): dag/nodes is the link to the live DAG, a landing writes the live files and
    md.git commits them in live, so a side commit carries no DAG delta and this copies nothing. For a side commit made
    before that (an old pending journal) the delivery's changes are merged field-wise into the current live node
    (_merge_fields) and committed in live. Nothing is refused: there are no promotion collisions any more."""
    lines, copied_all = {}, []
    if LIVE.resolve() == P.resolve():   # 2026-10-19: one repository; the landings committed everything here
        live = subprocess.check_output(["git", "rev-parse", "--short", "HEAD"], cwd=P, text=True).strip()
        return {head: f"PROMOTED {item} files 0 collisions 0 live {live}\n" for _, _, item, head in entries}
    with merge_lock(LIVE / "coord/.merge.lock"):
        per = []
        for commit, g, item, head in entries:
            parent = subprocess.check_output(["git", "rev-parse", commit + "^"], cwd=P, text=True).strip()
            files = subprocess.check_output(["git", "diff", "--name-only", parent, commit, "--", "dag/nodes"], cwd=P, text=True).splitlines()
            copied = []
            for rel in files:
                shown = subprocess.run(["git", "show", commit + ":" + rel], cwd=P, text=True, capture_output=True)
                if shown.returncode:
                    continue        # a deletion is never promoted
                after = json.loads(shown.stdout)
                prior = subprocess.run(["git", "show", parent + ":" + rel], cwd=P, text=True, capture_output=True)
                before = json.loads(prior.stdout) if prior.returncode == 0 else None
                dst = LIVE / rel
                current = json.loads(dst.read_text()) if dst.exists() else None
                out = _merge_fields(before, after, current)
                if out.get("id", "").startswith("nt-target-") or out.get("target") is True:
                    out.pop("target", None)
                if out == current:
                    continue
                dst.parent.mkdir(parents=True, exist_ok=True)
                dst.write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n"); copied.append(rel)
            per.append((head, item, len(copied)))
            copied_all += copied
        if copied_all and subprocess.check_output(["git", "diff", "--name-only", "--", *copied_all], cwd=LIVE, text=True).strip():
            subprocess.run(["git", "add", "-A", "--", *copied_all], cwd=LIVE, check=True)
            if len(entries) == 1:
                msg = f"Stage-1 shared landing {entries[0][2]} ({entries[0][1]})"
            else:
                msg = f"Stage-1 shared landing of {len(entries)} deliveries\n\n" + "".join(f"- {i} ({g})\n" for _, g, i, _ in entries)
            msg += "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
            subprocess.run(["git", "-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", "commit", "-q",
                            "--author=Bin Wu <844524296@qq.com>", "-m", msg, "--", *copied_all], cwd=LIVE, check=True,
                           env=dict(os.environ, SHEAF_LEAD="L-only"))
        live = subprocess.check_output(["git", "rev-parse", "--short", "HEAD"], cwd=LIVE, text=True).strip()
    for head, item, nc in per:
        lines[head] = f"PROMOTED {item} files {nc} collisions 0 live {live}\n"
    return lines


def replay_pending():
    """Side commits journalled before their promotion (a crash between the two, or the old collision journal)."""
    if not PENDING.exists():
        return
    ent = []
    for p in sorted(PENDING.glob("*.json"), key=lambda p: p.stat().st_mtime):
        r = json.loads(p.read_text()); ent.append((p.stem, r["g"], r["item"], r["head"]))
    if ent:
        say("replaying", len(ent), "unpromoted side commits")
        promote(ent)
        for c, _, _, _ in ent:
            (PENDING / (c + ".json")).unlink(missing_ok=True)


def main():
    rows = json.load(sys.stdin)
    results = {}
    _t0 = time.time(); _rt = {}
    try:
        replay_pending()
    except Exception:  # noqa: BLE001
        say("replay failed:", traceback.format_exc()[-500:])
    _rt["replay"] = time.time() - _t0; _t1 = time.time()
    todo, solo = [], []
    for row in rows:
        if row.get("verdict") not in ("PASS", "FIX"):
            solo.append(row); continue
        r = precheck(row)
        if r is not None:
            results[row["head"]] = r
        else:
            todo.append(row)
    _rt["precheck"] = time.time() - _t1; _t1 = time.time(); _rt["promote"] = 0.0
    notopen = []
    if todo:
        try:
            import live_closed      # fastland: fill the cache outside the side lock (stage1() under the lock reads it)
            live_closed.closed()
        except Exception:  # noqa: BLE001
            pass
    while todo:
        chunk, todo = todo[:SIZE], todo[SIZE:]
        again = []
        merged = land_chunk(chunk, results, notopen, again)
        if again:
            say(len(again), "rows deferred (file conflict in the round / chunk failure): no result, next round")
        if merged:
            ent = [(full, d["g"], d["item"], d["head"]) for d, full in merged]
            _tp = time.time()
            try:
                lines = promote(ent)
                _rt["promote"] += time.time() - _tp
                for c, g, item, head in ent:
                    line = lines.get(head, "")   # promote() and results are keyed by delivery head, not side commit
                    results[head]["stdout"] += line
                    if "collisions 0 " in line:
                        (PENDING / (c + ".json")).unlink(missing_ok=True)
                    else:
                        results[head]["rc"] = 1
                        results[head]["stderr"] += (
                            "promotion collision; pending journal retained for the next batch\n"
                        )
            except Exception:  # noqa: BLE001
                tb = traceback.format_exc()
                for _, _, _, h in ent:
                    results[h]["rc"] = 1; results[h]["stderr"] += "promotion failed (journalled, replayed next run):\n" + tb
        if todo:
            time.sleep(2)   # let other lock users in between chunks
    _rt["chunks"] = time.time() - _t1 - _rt["promote"]; _t1 = time.time()
    for row in notopen:      # not stage-1-open: retired at once, else refused (as tools/nt_land.py answers it)
        g, item, head = row["g"], row["item"], row["head"]
        if head in results:
            continue
        try:
            if retire_completed(g, item, head):
                results[head] = res(0, f"SUPERSEDED {item} completed stage-1 delivery archived; stale handoff retired\n")
            else:
                # 2026-10-18 (s1loop): say which copy disagrees; a completion only in this project's copy is L's to promote
                q = dag_queue.queue_node(item)
                why = ("completed in this project's DAG but not in the live DAG the queue reads (side completion never "
                       "promoted; L promotes it)" if q is not None and not dag_queue.stage1_completed(q)
                       else "no longer stage-1-open; live completion takes priority")
                results[head] = res(1, f"NOT MERGED {item}: {item}: {why}\n")
        except Exception as e:  # noqa: BLE001
            if "HEAD MOVED" in str(e):
                results[head] = res(1, f"HEAD MOVED/SUPERSEDED {item}\n")
            else:
                say("retire failed, stays queued:", item, str(e)[:300])
    for row in solo:         # RETURN verdicts only (a return, not a landing)
        if row["head"] not in results:
            results[row["head"]] = single(row)
    _rt["tail"] = time.time() - _t1
    try:
        with open(BL / "rounds.tsv", "a") as fh:
            fh.write(time.strftime("%F %T") + f"\t{len(rows)}\ttotal {time.time() - _t0:.1f}\t" + " ".join(f"{k} {v:.1f}" for k, v in _rt.items()) + "\n")
    except OSError:
        pass
    say("round:", sum(1 for r in results.values() if re.search(r"(?m)^MERGED ", r["stdout"])), "merged,", len(results),
        "decided of", len(rows), "rows; the rest stay queued")
    print("RESULTS_JSON " + json.dumps(results), flush=True)


if __name__ == "__main__":
    main()
