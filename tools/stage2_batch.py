#!/usr/bin/env python3
"""Stage-2 deliveries land in the batch of the stage-3 lander (the human, 2026-10-25): one landing pipeline.

A stage-2 delivery a reviewer passed (local/verdicts/2/<head>.json, status queued, verdict PASS or FIX) is checked
once, alone, as soon as its verdict is queued: tools/nt_land2.py --prepare-archive (the delivery's own split check,
import prune check, its node records; the worker compiled its modules before pushing). The result is kept by head in
local/batch/s2plans/<head>.json. tools/batch_land.py puts every checked delivery into its next batch next to the
stage-3 deliveries: the batch DAG check (tools/nt_incremental2.py and the split check over all stage-2 deliveries of
the batch) takes out only its offenders, each remaining delivery is written and committed as one landing, and the
global build verifies the batch; a red build gives the delivery that wrote a failing module back to its writer, the
rest lands. A delivery whose own files changed since its check is checked again; a RETURN verdict goes back to the
writer at once.

  tools/stage2_batch.py status              the queued verdicts and their checks
  tools/stage2_batch.py validate IN OUT     (internal) the batch DAG check of the plans in IN
"""
import json, os, pathlib, re, subprocess, sys, tarfile, tempfile, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import merge_delivery as md  # noqa: E402
import landing as ld  # noqa: E402
import stage3_delivery as s3  # noqa: E402
import leanindex as li  # noqa: E402

ROOT = md.ROOT
VQ = ROOT / "local" / "verdicts" / "2"
PL = ROOT / "local" / "batch" / "s2plans"
CHUNK = int(os.environ.get("SHEAF_S2_PREP_CHUNK", "48"))
JOBS = os.environ.get("SHEAF_S2_PREP_JOBS", "8")
TRIES = 5


class Stale(Exception):
    """The delivery is checked again before it can land."""


def _read(p):
    try:
        return json.loads(pathlib.Path(p).read_text())
    except (OSError, ValueError):
        return None


def _write(p, obj):
    p = pathlib.Path(p); p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_name(p.name + ".tmp%d" % os.getpid()); tmp.write_text(json.dumps(obj, indent=1, ensure_ascii=False)); tmp.replace(p)


def vq_update(head, **kw):
    """The verdict's status (the review service's queue, ~/weil-review-svc/vq.py)."""
    p = VQ / f"{head}.json"
    v = _read(p)
    if v is not None:
        v.update(kw); _write(p, v)


def queued():
    out = []
    for p in sorted(VQ.glob("*.json")) if VQ.is_dir() else []:
        v = _read(p)
        if v and v.get("status") == "queued" and v.get("system") == "cc" and re.fullmatch(r"[0-9a-f]{40}", str(v.get("head"))):
            out.append(v)
    return out


def listed():
    """The items coord/queue.tsv lists at stage 2 (only those are work, 2026-10-25); None when unreadable."""
    try:
        s = {l.split("\t")[0] for l in (ROOT / "coord" / "queue.tsv").read_text().splitlines()
             if not l.startswith("#") and l.count("\t") >= 1 and l.split("\t")[1] == "2"}
    except OSError:
        return None
    return s or None


def branch_head(g, item):
    return md.git("rev-parse", "-q", "--verify", f"refs/heads/deliver/{g}/{item}", check=False)


def plan_path(head):
    return PL / f"{head}.json"


def archive(g, item, head, kind):
    """The delivery branch is kept under refs/stage2-<kind>/ and removed (as tools/nt_parallel2.py did)."""
    ref = f"refs/heads/deliver/{g}/{item}"
    if branch_head(g, item) != head:
        return False
    md.git("update-ref", f"refs/stage2-{kind}/{g}/{item}/{head}", head)
    md.git("update-ref", "-d", ref, head)
    return True


def do_return(g, item, head, note, log):
    """The delivery goes back to its writer (coord/returns/<G>.md); True when done or no longer current."""
    if branch_head(g, item) != head:
        vq_update(head, status="superseded", land_output="branch moved or gone")
        plan_path(head).unlink(missing_ok=True); return True
    try:
        md.cmd_return(g, item, "L: independent stage-2 immutable head " + head[:12] + ": " + note)
        with md.merge_lock():
            archive(g, item, head, "returned")
    except md.Fail as e:
        log("stage 2: return not done, retried", g, item, head[:9], "|", str(e)[:200]); return False
    vq_update(head, status="returned", land_output=note[-800:])
    plan_path(head).unlink(missing_ok=True)
    log("stage 2: RETURNED", g, item, head[:9], "|", " ".join(note.split())[:200])
    return True


def row_of(v):
    return {"group": v["group"], "item": v["item"], "head": v["head"], "reviewer": "NT-stage2-cc-" + v["head"][:9],
            "note": (str(v.get("note") or "").strip() or "independent cc stage-2 review")[:6000],
            "verdict": v["verdict"], "drop_nodes": v.get("drop_nodes") or []}


def archive_input(vs):
    """The review files of the verdicts, as tools/nt_land2.py --prepare-archive reads them (svc.py _s2_archive)."""
    f = tempfile.TemporaryFile()
    rows = []
    with tarfile.open(fileobj=f, mode="w:") as tar:
        for v in vs:
            row = row_of(v)
            remote = "local/stage2/reviews/cc__" + v["group"] + "__" + v["item"] + "__" + v["head"][:12]
            rm = pathlib.Path(v.get("review_md") or "/nonexistent")
            if rm.is_file():
                tar.add(rm, arcname=remote + "/review.md")
            if v["verdict"] == "FIX":
                fx = pathlib.Path(v.get("fixes") or "/nonexistent")
                if fx.is_dir():
                    row["apply_fixes"] = remote + "/fixes"; tar.add(fx, arcname=remote + "/fixes")
            rows.append(row)
        payload = json.dumps(rows).encode(); ti = tarfile.TarInfo("manifest.json"); ti.size = len(payload)
        import io
        tar.addfile(ti, io.BytesIO(payload))
    f.seek(0)
    return f


class Prep:
    """The per-delivery checks, one background process for the verdicts waiting (at most CHUNK), never blocking a step."""

    def __init__(self):
        self.proc, self.out, self.vs, self.t0 = None, None, [], 0.0
        self.tries = {}

    def _retry(self, head):
        self.tries[head] = self.tries.get(head, 0) + 1
        return self.tries[head] <= TRIES

    def _collect(self, log):
        p, out, vs = self.proc, self.out, self.vs
        self.proc, self.out, self.vs = None, None, []
        text = out.read_text(errors="replace") if out.exists() else ""
        out.unlink(missing_ok=True)
        lines = [x[len("PLANS_JSON "):] for x in text.splitlines() if x.startswith("PLANS_JSON ")]
        if p.returncode or not lines:
            log(f"stage 2: checks of {len(vs)} deliveries failed (exit {p.returncode}), tried again |", text[-300:].replace("\n", " "))
            for v in vs:
                if not self._retry(v["head"]):
                    vq_update(v["head"], status="failed", land_output="check failed: " + text[-600:])
            return
        by = {v["head"]: v for v in vs}
        n = {"checked": 0, "returned": 0, "retry": 0, "failed": 0}
        for plan in json.loads(lines[-1]):
            row = plan.get("row") or {}
            head = row.get("head")
            if head not in by:
                continue
            if "id" in plan:
                _write(plan_path(head), plan); n["checked"] += 1
                # nt_parallel2.prepare keeps its own copy for its commit path (off since 2026-10-25): 7 GB on 10-25
                (ROOT / "local" / "stage2" / "parallel" / (plan["id"] + ".json")).unlink(missing_ok=True)
            elif plan.get("result") == "RETURN":
                do_return(row["group"], row["item"], head, str(plan.get("note") or "refused by the checks"), log); n["returned"] += 1
            elif self._retry(head):
                n["retry"] += 1
                log("stage 2: check to be repeated", row.get("item"), head[:9], "|", str(plan.get("note", ""))[-200:].replace("\n", " "))
            else:
                vq_update(head, status="failed", land_output="check: " + str(plan.get("note", ""))[-800:]); n["failed"] += 1
        log(f"stage 2: {len(vs)} deliveries checked in {time.time() - self.t0:.0f} s: {json.dumps(n)}")

    def pump(self, log):
        """Collect a finished check; return RETURN verdicts and drop superseded ones; start the next check."""
        if self.proc is not None and self.proc.poll() is not None:
            self._collect(log)
        L = listed()
        todo = []
        for v in queued():
            g, item, head = v["group"], v["item"], v["head"]
            if L is not None and item not in L:
                vq_update(head, status="superseded", land_output="no longer on the stage-2 queue (pruned plan node or stated meanwhile)")
                plan_path(head).unlink(missing_ok=True)
                log("stage 2: superseded (not on the stage-2 queue)", g, item, head[:9]); continue
            if branch_head(g, item) != head:
                vq_update(head, status="superseded", land_output="branch moved or gone")
                plan_path(head).unlink(missing_ok=True)
                log("stage 2: superseded (branch moved)", g, item, head[:9]); continue
            if v.get("verdict") == "RETURN":
                do_return(g, item, head, str(v.get("note") or "returned by the reviewer")[:6000], log); continue
            if v.get("verdict") not in ("PASS", "FIX") or plan_path(head).exists():
                continue
            if self.proc is not None and head in {x["head"] for x in self.vs}:
                continue
            todo.append(v)
        if self.proc is not None or not todo:
            return
        self.vs = todo[:CHUNK]
        PL.mkdir(parents=True, exist_ok=True)
        self.out = PL / "check.out"
        inp = archive_input(self.vs)
        self.t0 = time.time()
        self.proc = subprocess.Popen(["nice", "-n", "10", sys.executable, "-u", "tools/nt_land2.py", "--prepare-archive"], cwd=ROOT,
                                     stdin=inp, stdout=open(self.out, "w"), stderr=subprocess.STDOUT,
                                     env=dict(os.environ, SHEAF_LEAD="L-only", NT_CHECK_JOBS=JOBS))
        inp.close()
        log(f"stage 2: checking {len(self.vs)} delivery(ies) (pid {self.proc.pid})")

    def ready(self):
        """The checked plans of queued PASS/FIX verdicts whose branch is still at the checked head."""
        out = []
        for v in queued():
            if v.get("verdict") not in ("PASS", "FIX"):
                continue
            plan = _read(plan_path(v["head"]))
            if not plan or "id" not in plan or (plan.get("row") or {}).get("head") != v["head"]:
                continue
            if branch_head(v["group"], v["item"]) != v["head"]:
                continue
            out.append(plan)
        return out


def paths_of(plan):
    return sorted(plan["writes"])


def modules_of(plan):
    return {m["module"]: plan["writes"][m["file"]] for m in plan["modules"]}


def validate(plans, log):
    """The batch DAG check (tools/nt_parallel2.validated_survivors: tools/nt_incremental2.py over all stage-2
    deliveries of the batch, and the split check); the offenders go back to their writers. Returns the survivors."""
    if not plans:
        return []
    with tempfile.TemporaryDirectory(prefix="sheaf-s2v-") as td:
        a, b = pathlib.Path(td) / "in.json", pathlib.Path(td) / "out.json"
        a.write_text(json.dumps(plans))
        r = subprocess.run([sys.executable, str(pathlib.Path(__file__).resolve()), "validate", str(a), str(b)], cwd=ROOT,
                           capture_output=True, text=True, timeout=1800)
        res = _read(b)
    if r.returncode or res is None:
        log("stage 2: batch DAG check failed; the stage-2 deliveries wait for the next batch |", (r.stdout + r.stderr)[-300:].replace("\n", " "))
        return []
    if res.get("error"):
        log("stage 2: batch DAG check unattributed; the stage-2 deliveries wait for the next batch |", res["error"][:300])
        return []
    for head, note in res["returns"]:
        p = next(p for p in plans if p["row"]["head"] == head)
        do_return(p["row"]["group"], p["row"]["item"], head, note, log)
    ok = set(res["ok"])
    return [p for p in plans if p["id"] in ok]


def land_one(plan, batch_id):
    """Write, register and commit one stage-2 delivery. Called with coord/.merge.lock held."""
    row = plan["row"]
    g, item, head, reviewer = row["group"], row["item"], row["head"], row["reviewer"]
    if branch_head(g, item) != head:
        raise Stale("the branch moved after the checks")
    stale = [rel for rel, old in plan["expected"].items() if ((ROOT / rel).read_text() if (ROOT / rel).is_file() else None) != old]
    if stale:
        plan_path(head).unlink(missing_ok=True)
        raise Stale("changed since its check, checked again: " + ", ".join(stale[:5]))
    lean = [rel for rel in plan["writes"] if rel.startswith("lean/") and rel.endswith(".lean")]
    rels = [rel[len("lean/"):] for rel in lean]
    landing = None
    if rels:
        r = subprocess.run([sys.executable, "tools/landing.py", "begin", g, *rels], cwd=ROOT, capture_output=True, text=True)
        if r.returncode != 0:
            raise Stale("landing.py begin: " + (r.stderr or r.stdout).strip()[:300])
        landing = r.stdout.strip().splitlines()[-1]
    tree, book, done, kind = md.Tree(), {"group": g, "item": item}, False, "dag"
    try:
        for rel in lean:
            p = ROOT / rel; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(plan["writes"][rel])
        if landing:
            r = subprocess.run([sys.executable, "tools/landing.py", "finish", landing] + (["--set"] if len(rels) > 1 else []),
                               cwd=ROOT, capture_output=True, text=True)
            if r.returncode != 0:
                raise md.Fail("landing.py finish: " + (r.stderr or r.stdout).strip()[:300])
            done = True
            kind = r.stdout.strip().splitlines()[-1]
            req = ld.REQUESTS / f"{landing}.json"
            rec = ld.read_json(req) or {}
            # statements: every `sorry` of the delivered modules is the stage's own (the build's probe checks the rest)
            allowed = {m["module"]: sorted(k for k, d in s3.decl_table(plan["writes"][m["file"]]).items() if d["sorry"])
                       for m in plan["modules"]}
            rec.update(batch=batch_id, delivery={"group": g, "item": item, "head": head}, stage=2, sorry_allowed=allowed)
            ld.write_json(req, rec)
        paths = list(lean)
        for rel, text in plan["writes"].items():
            if rel not in lean:
                tree.write(rel, text); paths.append(rel)
        rp, rtext, parts = md.return_entries(g, item)
        keep = [x for x in parts if not x.startswith(f"## {item} (")]
        book["returns"] = (rp, rtext)
        if rtext is not None and len(keep) != len(parts):
            rp.write_text("".join(keep)); paths.append(rp.relative_to(ROOT).as_posix())
        claim = ROOT / "coord" / "claims" / (item.replace("/", "__") + ".lock")
        claim_text = claim.read_text() if claim.exists() else None
        book["claim"] = (claim, claim_text)
        dlog = ROOT / "coord" / "deliveries.log"
        book["dlog"] = (dlog, dlog.read_text() if dlog.exists() else "")
        subprocess.run([sys.executable, "tools/claim.py", "done", g, item,
                        f"delivered by {g} on deliver/{g}/{item}, merged by L (reviewer {reviewer})"], cwd=ROOT, capture_output=True)
        book["ledger"] = md.ledger_line(plan["ledger"] + f"; batch {batch_id}; landing {landing or '-'} ({kind})")
        paths += ["coord/ledger.md", "coord/deliveries.log"]
        if claim_text is not None and md.exists_at("HEAD", claim.relative_to(ROOT).as_posix()):
            paths.append(claim.relative_to(ROOT).as_posix())
        note = ROOT / "coord" / "repair-notes" / (item + ".json")
        if note.exists() and md.git("status", "--porcelain", "--", note.relative_to(ROOT).as_posix()).strip():
            paths.append(note.relative_to(ROOT).as_posix())
        md.git_retry("add", "-A", "--", *paths)
        md.git_retry("commit", "-q", "-m", plan["message"] + f"\n\nStage-2 delivery of {g} (deliver/{g}/{item}, head {head[:12]}); "
                     f"landing {landing or '-'} ({kind}); batch {batch_id}, which the global build verifies; merged by "
                     "tools/batch_land.py for L.", "--", *paths)
    except BaseException:
        tree.restore(); md.unbook(book)
        if landing and done:
            with ld.tree_lock():          # nothing committed: the files back to their version before this landing
                dropped, restore_to, _ = ld.drop_plan([landing])
                for rel, data in restore_to.items():
                    dst = li.LEAN / rel
                    if data is None: dst.unlink(missing_ok=True)
                    else: dst.write_bytes(data)
                ld.drop_close(dropped, "the batch landing did not commit")
        elif landing:
            subprocess.run([sys.executable, "tools/landing.py", "abort", landing], cwd=ROOT, capture_output=True)
        raise
    sha = md.git("rev-parse", "HEAD")
    archive(g, item, head, "landed")
    vq_update(head, status="landed", land_output=f"batch {batch_id}, landing {landing or '-'}, commit {sha[:10]}; the global build verifies it")
    plan_path(head).unlink(missing_ok=True)
    return {"group": g, "item": item, "head": head, "reviewer": reviewer, "landing": landing, "kind": kind, "commit": sha,
            "overrides": {}, "modules": [m["module"] for m in plan["modules"]], "claim": claim_text,
            "state": "landed" if landing else "verified", "stage": "2", "verdict": row.get("verdict", "PASS")}


def requeue(e):
    """A stage-2 entry deferred by a red build: its branch back, its verdict queued again (checked again)."""
    br = f"refs/heads/deliver/{e['group']}/{e['item']}"
    if not md.has_ref(br):
        md.git("update-ref", br, e["head"])
    plan_path(e["head"]).unlink(missing_ok=True)
    vq_update(e["head"], status="queued", land_output="deferred by a red build of its batch; checked and landed again")


def mark_out(e):
    """A stage-2 entry taken out of its batch (returned to its writer, or reverted): its verdict says so."""
    if e.get("stage") == "2" and not e.get("vq_marked"):
        vq_update(e["head"], status="returned", land_output=("taken out of the batch: " + str(e.get("why") or ""))[:800])
        e["vq_marked"] = True


def cmd_validate(a, b):
    import nt_parallel2 as npl
    plans = json.loads(pathlib.Path(a).read_text())
    npl.freeze_config()
    returns = []
    try:
        ok = npl.validated_survivors(plans, returns)
        _write(b, {"ok": [p["id"] for p in ok], "returns": [[row["head"], note] for row, note in returns]})
    except md.Fail as e:
        _write(b, {"error": str(e), "ok": [], "returns": []})
    return 0


def main(a):
    if len(a) == 3 and a[0] == "validate":
        return cmd_validate(a[1], a[2])
    if a == ["status"]:
        L = listed()
        for v in queued():
            st = "checked" if plan_path(v["head"]).exists() else "waiting for its check"
            if L is not None and v["item"] not in L: st = "not on the stage-2 queue"
            print(f"{v['verdict']:6} {v['group']}/{v['item']} {v['head'][:9]} {st}")
        return 0
    print(__doc__); return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
