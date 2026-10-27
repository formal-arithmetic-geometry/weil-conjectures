#!/usr/bin/env python3
"""tools/freeze.py and tools/rework.py blocked_count on a mock repository (temporary git repo, mock rework rows).
Run: python3 tools/test_freeze.py"""
import json, os, pathlib, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rework  # noqa: E402
import freeze  # noqa: E402

fails = 0


def check(name, got, want):
    global fails
    ok = got == want
    fails += not ok
    print(("ok  " if ok else "FAIL") + f" {name}" + ("" if ok else f": got {got!r}, want {want!r}"))


def put(root, rel, text="-- x\n"):
    p = root / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)


def git(root, *a):
    return subprocess.run(["git", *a], cwd=root, capture_output=True, text=True, check=True).stdout.strip()


with tempfile.TemporaryDirectory(prefix="freeze-test-") as d:
    R = pathlib.Path(d)
    git(R, "init", "-q")
    git(R, "config", "user.email", "t@t"); git(R, "config", "user.name", "t")
    rework.ROOT, rework.QDIR, rework.FILE = R, R / "quarantine", R / "coord" / "rework.tsv"
    rework.TRIED = R / "local" / "rework-tried.json"
    freeze.ROOT, freeze.STATE, freeze.LAST = R, R / "local/batch/freeze.json", R / "local/builds/last.json"
    freeze.CLAIMS, freeze.SIGNAL, freeze.LOG = R / "coord/claims", R / "cc1/FREEZE", R / "cc1/freeze.log"
    os.environ["SHEAF_FREEZE_BLOCKED"] = "2"
    # mock rework rows: Root (an error root, claimed), Imp1 and Imp2 import it, Fixed is back in lean/
    rows = {"Sheaf.Root": "error: boom", "Sheaf.Imp1": "imports Sheaf.Root", "Sheaf.Imp2": "imports Sheaf.Imp1",
            "Sheaf.Fixed": "error: old"}
    texts = {"Sheaf.Root": "import Mathlib\n", "Sheaf.Imp1": "import Sheaf.Root\n", "Sheaf.Imp2": "import Sheaf.Imp1\n",
             "Sheaf.Fixed": "import Mathlib\n"}
    for m, t in texts.items():
        put(R, rework.qpath(m), t)
    put(R, rework.opath("Sheaf.Fixed"))
    put(R, "quarantine/Sheaf/NoRow.lean")       # a quarantined copy without a row: blocked too
    (R / "coord").mkdir(exist_ok=True)
    rework.save({m: {"module": m, "original": rework.opath(m), "quarantine": rework.qpath(m), "sync": "t",
                     "time": "2026-10-28T00:00:00Z", "cause": c} for m, c in rows.items()})
    put(R, "coord/claims/Sheaf.Root.lock", json.dumps({"who": "G3", "t": 1793145600 - 7200}))
    git(R, "add", "-A"); git(R, "commit", "-qm", "c1")
    c1 = git(R, "rev-parse", "HEAD")

    check("blocked files", rework.blocked_files(), ["quarantine/Sheaf/Imp1.lean", "quarantine/Sheaf/Imp2.lean",
                                                     "quarantine/Sheaf/NoRow.lean", "quarantine/Sheaf/Root.lean"])
    check("blocked count", rework.blocked_count(), 4)
    check("blocked count of a commit", rework.blocked_count(c1), 4)

    rs = freeze.roots(now=1793145600)
    check("roots", [(r["module"], r["kind"], r["waiting"], r["claimant"], r["claim_age"]) for r in rs],
          [("Sheaf.Root", "restorable", 2, "G3", "2.0h")])
    import hashlib
    put(R, "local/rework-tried.json", json.dumps({"Sheaf.Root": hashlib.sha1(texts["Sheaf.Root"].encode()).hexdigest()}))
    check("root confirmed unfixed", [r["kind"] for r in freeze.roots(now=1793145600)], ["unfixed error"])

    # filter: only rework items (and maintainer groups) pass
    cands = [{"group": "Q1", "item": "Sheaf.Root"}, {"group": "Q2", "item": "Sheaf.Other"},
             {"group": "L", "item": "Sheaf.Maint"}, {"group": "Q3", "item": "Sheaf.Imp1"}]
    keep, wait = freeze.split(cands)
    check("split keep", [c["item"] for c in keep], ["Sheaf.Root", "Sheaf.Maint", "Sheaf.Imp1"])
    check("split wait", [c["item"] for c in wait], ["Sheaf.Other"])

    logs = []
    st = freeze.update(logs.append, now=1793145600)
    check("frozen above the limit", (st["frozen"], st["blocked"]), (True, 4))
    check("signal written", freeze.SIGNAL.exists(), True)
    line = freeze.SIGNAL.read_text()
    check("signal one line", line.count("\n"), 1)
    check("signal names the root and claimant", ("Sheaf.Root" in line, "claim G3" in line, "blocked 4 > 2" in line,
                                                 "1 without a rework row" in line), (True, True, True, True))
    check("lander log", any(x.startswith("frozen: 4 blocked") for x in logs), True)
    check("frozen()", freeze.frozen(), True)

    # batch_land's filter follows the state
    try:
        import batch_land as bl
        got = [c["item"] for c in bl.freeze_filter(list(cands))]
        check("batch_land filter frozen", (got, bl.FROZEN.get("wait"), bl.FROZEN.get("blocked")),
              (["Sheaf.Root", "Sheaf.Maint", "Sheaf.Imp1"], 1, 4))
    except ImportError as exc:
        print("skip batch_land filter (not importable here):", exc)
        bl = None

    # the root fix and the restore land: blocked 0 in the working tree, but no green build of it yet -> still frozen
    for m in ("Sheaf.Root", "Sheaf.Imp1", "Sheaf.Imp2"):
        put(R, rework.opath(m), texts[m])
    (R / "quarantine/Sheaf/NoRow.lean").unlink()
    put(R, "local/builds/last.json", json.dumps({"result": "green", "commit": c1, "time": "old"}))
    st = freeze.update(logs.append, now=1793145700)
    check("still frozen: the green build is older", (st["frozen"], st["blocked"], bool(st.get("low_head"))), (True, 0, True))
    git(R, "add", "-A"); git(R, "commit", "-qm", "c2")
    c2 = git(R, "rev-parse", "HEAD")
    put(R, "local/builds/last.json", json.dumps({"result": "red", "commit": c2, "time": "red"}))
    st = freeze.update(logs.append, now=1793145800)
    check("still frozen: red build", st["frozen"], True)
    # a green build of a commit with too many blocked (low_head is c1 here: simulate by a green build of c1's tree
    # descendant that still has the quarantined files)
    put(R, "local/builds/last.json", json.dumps({"result": "green", "commit": c2, "time": "green"}))
    st = freeze.update(logs.append, now=1793145900)
    check("unfrozen after a green build", (st["frozen"], freeze.SIGNAL.exists()), (False, False))
    check("freeze.log has on and off", [("FREEZE on" in l, "FREEZE off" in l) for l in freeze.LOG.read_text().splitlines()
                                        if "FREEZE" in l], [(True, False), (False, True)])
    if bl is not None:
        check("batch_land filter unfrozen", ([c["item"] for c in bl.freeze_filter(list(cands))], bl.FROZEN),
              (["Sheaf.Root", "Sheaf.Other", "Sheaf.Maint", "Sheaf.Imp1"], {}))

    # a green build whose own tree is still above the limit does not unfreeze
    for m in ("Sheaf.Root", "Sheaf.Imp1", "Sheaf.Imp2"):
        (R / rework.opath(m)).unlink()
    st = freeze.update(logs.append, now=1793146000)
    check("frozen again", st["frozen"], True)
    git(R, "add", "-A"); git(R, "commit", "-qm", "c3 (3 blocked)")
    c3 = git(R, "rev-parse", "HEAD")
    put(R, "local/builds/last.json", json.dumps({"result": "green", "commit": c3, "time": "green3"}))
    check("blocked count of c3", rework.blocked_count(c3), 3)
    for m in ("Sheaf.Root", "Sheaf.Imp1", "Sheaf.Imp2"):
        put(R, rework.opath(m), texts[m])
    st = freeze.update(logs.append, now=1793146100)        # low_head = c3; the green build of c3 has 3 blocked
    check("green build above the limit keeps the freeze", (st["frozen"], st["blocked"]), (True, 0))

print("FAILED" if fails else "all ok", fails)
sys.exit(1 if fails else 0)
