#!/usr/bin/env python3
"""tools/rework_drift.py: the pure parts (no git, no Lean). Run: python3 tools/test_rework_drift.py"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rework_drift as rd  # noqa: E402

fails = 0


def check(name, got, want):
    global fails
    ok = got == want
    fails += not ok
    print(("ok  " if ok else "FAIL") + f" {name}" + ("" if ok else f": got {got!r}, want {want!r}"))


# classify: own error FAIL; a failed earlier job DEP; missing object of another module INFRA; slow; no slot
check("ok", rd.classify({"rc": 0}, set()), "OK")
check("own error", rd.classify({"rc": 1, "out": "X.lean:3:4: error: unsolved goals"}, set()), "FAIL")
check("dep failed", rd.classify({"rc": 1, "out": "error: object file /a/B.olean of module Sheaf.B does not exist"},
                                {"Sheaf.B"}), "DEP")
check("missing other", rd.classify({"rc": 1, "out": "error: object file /a/B.olean of module Sheaf.B does not exist"},
                                   set()), "INFRA")
check("slow", rd.classify({"rc": 124, "out": "NOT ACCEPTED"}, set()), "SLOW")
check("no slot", rd.classify({"rc": None, "out": "not compiled"}, set()), "INFRA")
check("overlay", rd.classify({"rc": 1, "out": "Dependency source unavailable: x"}, set()), "INFRA")

# importers_within: the quarantined importers (transitively) among the planned ones
rimp = {"A": set(), "B": {"A"}, "C": {"B"}, "D": {"X"}}
check("importers", rd.importers_within({"A"}, rimp, {"A", "B", "C", "D"}), {"A", "B", "C"})
check("importers among", rd.importers_within({"A"}, rimp, {"A", "C"}), {"A"})

# tokens: components and consecutive pairs, comments ignored
tk = rd.tokens("theorem t : Foo.map x = y -- hasSheafify\n/- Additive -/ example : IsIso f := rfl")
check("tokens", ("map" in tk, "Foo.map" in tk, "hasSheafify" in tk, "Additive" in tk, "IsIso" in tk),
      (True, True, False, False, True))

# reach_bits: the changed modules in the import closure, project modules only
g = {"Sheaf.Q": {"Sheaf.A", "Mathlib.X"}, "Sheaf.A": {"Sheaf.B"}, "Sheaf.B": set(), "Mathlib.X": {"Sheaf.C"}}
idx = {"Sheaf.B": 0, "Sheaf.C": 1}
check("reach", rd.reach_bits(["Sheaf.Q"], g, idx)["Sheaf.Q"], 1)

# message: the scratch path is removed
check("message", rd.message("/home/u/cc1/rset-tmp/c-ab12/lean/Sheaf/Q.lean:3:1: error: boom\n  detail"),
      "Sheaf/Q.lean:3:1: error: boom | detail")

# topo: an import first
check("topo", rd.topo({"A", "B", "C"}, {"C": {"B"}, "B": {"A"}}), ["A", "B", "C"])

print("FAILED" if fails else "all passed"); sys.exit(1 if fails else 0)
