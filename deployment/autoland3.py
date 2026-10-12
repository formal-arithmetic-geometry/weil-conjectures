#!/usr/bin/env python3
"""Lands the stage-3 deliveries that need no reader (tools/review_class.py: AUTO, including compiler-only) and those a
reader passed (tools/merge_delivery.py --stage 3 records the pass), in BATCHES (decision of the human, 2026-10-12): no
compile on the server, one write of the whole batch under coord/.merge.lock, and the global build of ~/cc1/buildloop.sh
verifies the batch. Each pass of the loop is one step of tools/batch_land.py: land a batch; wait for the build; green:
the batch is closed; red: the deliveries at fault are taken out again and returned to their groups with the compiler's
message (the tools decide what has one possible cause, an independent Codex agent on the groups' machine the rest, see
~/weil-launcher/xtriage.py there), and the next build decides again, at most three rounds. A delivery the static checks
refuse is returned to its group with the tools' message; a busy lock is tried again; a branch whose head moved is taken
with its new head. Any stage-2 delivery still coming in (the item is a node id) is landed one by one with
tools/merge_delivery.py --stage 2, as before.
Stop: kill $(cat ~/cc1/autoland.pid) (it stops between two steps). Log: ~/cc1/autoland.log. State: local/batch/ of the
repository (tools/batch_land.py status). AUTOLAND_ROOT names another repository (rehearsal)."""
import json, os, pathlib, signal, subprocess, sys, time
H = pathlib.Path.home(); ROOT = pathlib.Path(os.environ.get("AUTOLAND_ROOT") or H / "weil-conjectures-sheaf")
LOG = pathlib.Path(os.environ.get("AUTOLAND_LOG") or H / "cc1" / "autoland.log")
PID = pathlib.Path(os.environ.get("AUTOLAND_PID") or H / "cc1" / "autoland.pid")
os.environ["SHEAF_LEAD"] = "L-only"; os.environ["PATH"] = str(H / ".elan" / "bin") + ":" + os.environ.get("PATH", "")
# Load server settings on every launch; retain explicitly supplied overrides.
import shlex
for line in (ROOT / 'coord/sheaf.env').read_text().splitlines():
    fields = shlex.split(line, comments=True)
    if fields and '=' in fields[0]:
        name, value = fields[0].split('=', 1)
        os.environ.setdefault(name, value)
os.environ.setdefault('SHEAF_BATCH_POOL', '20')
sys.path.insert(0, str(ROOT / "tools")); import review_class as rc, batch_land as bl
ENV = dict(os.environ)
NOTE2 = "AUTO: landed after the second Codex reading and the tool's mechanical checks and compile; not read by a reviewer (tiered review, decision of the human 2026-10-11)"
STOP = []
def log(*a):
    with open(LOG, "a") as f: f.write(time.strftime("%F %T ") + " ".join(str(x) for x in a) + "\n")
seen = {}                                        # head -> class: a delivery is classified once per head
def stage2(tried):
    for g, item in rc.branches():
        if "." in item: continue                 # a stage-3 item is a module: the batch's
        h = rc.git("rev-parse", f"deliver/{g}/{item}").strip()
        if seen.get(h, "AUTO") != "AUTO" or h in tried: continue
        try: c, why, head = rc.classify(g, item)
        except Exception as e: log("classify error", g, item, repr(e)[:200]); continue
        seen[head] = c
        if c != "AUTO" or head in tried: continue
        cl = ROOT / "coord" / "claims" / f"{item}.lock"
        try:
            if json.loads(cl.read_text()).get("who") != g: continue
        except Exception: continue
        tried.add(head)
        try:
            p = subprocess.run([sys.executable, "tools/merge_delivery.py", g, item, "--stage", "2", "--reviewer", "AUTO", "--head", head, "--verdict", "PASS",
                                "--spot-checked", NOTE2], cwd=ROOT, env=ENV, capture_output=True, text=True, timeout=900)
            rcode, out = p.returncode, (p.stdout + p.stderr)
        except subprocess.TimeoutExpired: rcode, out = 124, "timeout"
        if rcode == 0: log("landed", g, item, head[:9], "stage 2"); continue
        why = " ".join(out.strip().split("\n")[-3:])[:400].replace("\t", " ")
        if "merge.lock held" in why: tried.discard(head); log("lock busy, will retry", g, item, head[:9]); continue
        if "the branch head is" in out: log("branch moved during the landing, new head is taken next", g, item, head[:9]); continue
        (ROOT / "local").mkdir(exist_ok=True)
        with open(ROOT / "local" / "autoland-failed.tsv", "a") as f: f.write(f"{g}\t{item}\t{head[:12]}\t{why}\n")
        log("FAILED, handed to a reader", g, item, head[:9], "|", why[:300])
def main():
    if "--once" in sys.argv: print(bl.step({}, log)); return
    PID.write_text(str(os.getpid())); log("autoland3 started on", ROOT, "(batch landing)")
    signal.signal(signal.SIGTERM, lambda *_: STOP.append(1))
    cache, tried = {"_pre": bl.Pre()}, set()     # the checks of the next batch run while the open one is built
    while not STOP:
        st = "idle"
        try: st = bl.step(cache, log)
        except Exception as e:
            if "merge.lock held" in str(e): log("lock busy, will retry")
            else:
                from pipeline_guard import alert
                batch = bl.read_json(bl.OPEN) or bl.read_json(bl.BD / 'landing.json') or {}
                alert(batch.get('id'), '?', 'batch step failed: ' + repr(e)[:300], 'repair or withdraw transaction')
                log("step error", repr(e)[:400])
        if STOP: break
        try: stage2(tried)
        except Exception as e: log("stage-2 error", repr(e)[:300])
        for _ in range(5 if st in ("landed", "verified", "returned") else 15):
            if STOP: break
            time.sleep(1)
    log("autoland3 stopped")
if __name__ == "__main__": main()
