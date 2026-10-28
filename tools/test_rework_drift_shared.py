#!/usr/bin/env python3
"""tools/rework_drift.py shared pre-compile: a quarantined chain shared by several candidates is compiled once, its
outputs are reused while the keys (text + imported keys) are unchanged, a failure makes its importers DEP, a slow file
(over the 60 s rule, compiled) is SLOW and its importers still compile (compiler faked).
Run: python3 tools/test_rework_drift_shared.py"""
import os, pathlib, sys, tempfile, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rework_drift as rd  # noqa: E402

fails = 0


def check(name, got, want):
    global fails
    ok = got == want
    fails += not ok
    print(("ok  " if ok else "FAIL") + f" {name}" + ("" if ok else f": got {got!r}, want {want!r}"))


calls = []


def fake_run(rel, src_root, out_root):
    calls.append(rel)
    text = (src_root / rel).read_text()
    o = out_root / rel[:-5]
    o.parent.mkdir(parents=True, exist_ok=True)
    if "BAD" in text:
        return {"rc": 1, "out": f"{rel}:1:1: error: boom", "secs": 0.1}
    (pathlib.Path(str(o) + ".olean")).write_text("olean")
    return {"rc": 0, "out": "", "secs": 61.0 if "SLOW" in text else 0.1}


with tempfile.TemporaryDirectory() as td:
    td = pathlib.Path(td)
    q = td / "q"
    # chain A <- B <- C, candidates C1, C2, C3 each import C; D imports a failing E; F imports a slow S
    g = {"S.B": {"S.A"}, "S.C": {"S.B"}, "S.C1": {"S.C", "Mathlib.X"}, "S.C2": {"S.C"}, "S.C3": {"S.C"},
         "S.D": {"S.E"}, "S.F": {"S.S"}}
    texts = {m: f"-- {m}\n" for m in ["S.A", "S.B", "S.C", "S.C1", "S.C2", "S.C3", "S.D", "S.F"]}
    texts["S.E"] = "-- BAD\n"
    texts["S.S"] = "-- SLOW\n"
    src = {}
    for m, t in texts.items():
        p = q / (m.replace(".", "/") + ".lean"); p.parent.mkdir(parents=True, exist_ok=True); p.write_text(t)
        src[m] = p
    live = set(texts)
    rows = {m: {"quarantine": str(src[m])} for m in texts}

    order, srcs = rd.shared_plan(["S.C1", "S.C2", "S.C3", "S.D", "S.F"], rows, g, live,
                                 has_pub=lambda m: True, lean_text=lambda m: False)
    check("plan: closure once", sorted(order), sorted(texts))
    check("plan: import order", order.index("S.A") < order.index("S.B") < order.index("S.C") < order.index("S.C1"), True)
    srcs = {m: src[m] for m in order}   # absolute fixture paths

    tree = td / "tree"
    res = rd.shared_compile(order, srcs, g, tree, time.time() + 600, parallel=4, run=fake_run)
    check("each module compiled once (the importer of a failure not at all)", sorted(calls),
          sorted(m.replace(".", "/") + ".lean" for m in texts if m != "S.D"))
    check("candidates OK", [res[m]["status"] for m in ["S.C1", "S.C2", "S.C3"]], ["OK", "OK", "OK"])
    check("own failure", res["S.E"]["status"], "FAIL")
    check("importer of failure", res["S.D"]["status"], "DEP")
    check("slow but compiled", res["S.S"]["status"], "SLOW")
    check("importer of slow compiles", res["S.F"]["status"], "OK")

    calls.clear()
    res = rd.shared_compile(order, srcs, g, tree, time.time() + 600, parallel=4, run=fake_run)
    check("second run: OK modules reused", sorted(calls), ["S/E.lean", "S/S.lean"])
    check("second run: reused flagged", res["S.C2"]["reused"], True)

    calls.clear()
    src["S.B"].write_text("-- S.B changed\n")
    res = rd.shared_compile(order, srcs, g, tree, time.time() + 600, parallel=4, run=fake_run)
    check("changed text: it and its importers again",
          sorted(c for c in calls if c not in ("S/E.lean", "S/S.lean")),
          ["S/B.lean", "S/C.lean", "S/C1.lean", "S/C2.lean", "S/C3.lean"])

    calls.clear()
    res = rd.shared_compile(order, srcs, g, tree, time.time() - 1, parallel=2, run=fake_run)
    check("past the deadline: not run", (calls, res["S.A"]["status"]), ([], "NOT RUN"))

print("FAILED" if fails else "all passed"); sys.exit(1 if fails else 0)
