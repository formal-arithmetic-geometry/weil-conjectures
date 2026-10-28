#!/usr/bin/env python3
"""Tests of tools/batch_pairs.py on synthetic batches (no Lean: the compile is a stub). The first one is the pattern of
red build 375085fafa (2026-10-28 08:56 CST): E5 adds a hypothesis to a theorem of ChainData; K8, in the same batch,
delivers the proof of KFlatFlat, which now imports ChainData (on main KFlatFlat is a sorry stub without that import)."""
import pathlib, sys, tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import batch_pairs as bp  # noqa: E402
import related_modules as rm  # noqa: E402


def mod(body: str, imports=()) -> str:
    return ("module\n\n" + "".join(f"public import {i}\n" for i in imports) + "\n@[expose] public section\n\n"
            "namespace Foo\n\n" + body + "\nend Foo\n")


CHAIN_OLD = mod("theorem native_weil_tensor_ringed_chain_data (n : Nat) : n = n := by\n  rfl\n")
CHAIN_NEW = mod("theorem native_weil_tensor_ringed_chain_data (n : Nat) (hsign : 0 < n) : n = n := by\n  rfl\n")
KFLAT_OLD = mod("theorem kflat_flat : True := by\n  sorry\n")
KFLAT_NEW = mod("theorem kflat_flat : True := by\n  have := native_weil_tensor_ringed_chain_data 1\n  trivial\n",
                ["Sheaf.ChainData"])
OTHER_OLD = mod("theorem other_thing : 1 = 1 := by\n  rfl\n")
OTHER_NEW = mod("theorem other_thing : 1 = 1 := by\n  simp\n")
MAIN = {"Sheaf.ChainData": CHAIN_OLD, "Sheaf.KFlatFlat": KFLAT_OLD, "Sheaf.Other": OTHER_OLD}


def plan(g, item, head, old, new, role="item"):
    return {"group": g, "item": item, "head": head, "D": {"modules": [{"module": item, "old": old, "text": new, "role": role}]}}


E5 = lambda: plan("E5", "Sheaf.ChainData", "e5" * 20, CHAIN_OLD, CHAIN_NEW)
K8 = lambda: plan("K8", "Sheaf.KFlatFlat", "k8" * 20, KFLAT_OLD, KFLAT_NEW)
C1 = lambda: plan("C1", "Sheaf.Other", "c1" * 20, OTHER_OLD, OTHER_NEW)


def combined(plans, main=MAIN):
    g = rm.graph_of_texts(main)
    for p in plans:
        g = rm.with_new_texts(g, bp.changes_of(p["D"]))
    return g


class Stub:
    """compile stub: B fails with A (its call uses A's hypothesis-free form), compiles alone"""
    def __init__(self, with_="FAIL", without="OK"):
        self.calls, self.with_, self.without = [], with_, without

    def __call__(self, a_texts, b_texts, mods, deadline, a_old=None):
        assert a_old is not None and set(a_old) <= set(a_texts), a_old
        self.calls.append((sorted(a_texts), sorted(b_texts), mods))
        r = {"with": self.with_, "with_out": "error: Tactic `rcases` failed" if self.with_ == "FAIL" else "", "without": None}
        if self.with_ == "FAIL":
            r["without"] = self.without
        return r


def run(plans, stub, source=None, now=None, main=MAIN):
    import time
    logs = []
    out = bp.split(plans, combined(plans, main), lambda *a: logs.append(" ".join(map(str, a))), compile=stub,
                   source=source or main.get, now=now or time.time)
    return out, logs


_TMP = tempfile.TemporaryDirectory(prefix="batch-pairs-test-")     # removed at exit


def fresh():
    bp.DIR = pathlib.Path(tempfile.mkdtemp(dir=_TMP.name))


def test_e5_k8_pattern_later_is_returned():
    fresh()
    stub = Stub()
    (land, waits, rets), _ = run([E5(), C1(), K8()], stub)
    assert [p["group"] for p in land] == ["E5", "C1"], land
    assert not waits, waits
    assert [p["group"] for p, _w in rets] == ["K8"], rets
    assert "Tactic `rcases` failed" in rets[0][1] and "E5/Sheaf.ChainData" in rets[0][1], rets[0][1]
    # only the linked pair is compiled (C1 is proof-only and unrelated)
    assert stub.calls == [(["Sheaf.ChainData"], ["Sheaf.KFlatFlat"], ["Sheaf.KFlatFlat"])], stub.calls


def test_links_only_with_a_name_or_import_link():
    g = combined([E5(), C1(), K8()])
    parties = [{"texts": bp.texts_of(p["D"]), "changes": bp.changes_of(p["D"]), "landing": True} for p in (E5(), C1(), K8())]
    L = bp.links(parties, g)
    assert [(x["a"], x["b"], x["modules"]) for x in L] == [(0, 2, ["Sheaf.KFlatFlat"])], L


def test_later_is_a_waits_earlier_b_lands():
    fresh()
    stub = Stub()
    (land, waits, rets), _ = run([K8(), E5()], stub)
    assert [p["group"] for p in land] == ["K8"], land
    assert [p["group"] for p, _w in waits] == ["E5"] and not rets, (waits, rets)


def test_compiles_together_lands_together_and_is_cached():
    fresh()
    stub = Stub(with_="OK")
    (land, waits, rets), _ = run([E5(), K8()], stub)
    assert [p["group"] for p in land] == ["E5", "K8"] and not waits and not rets
    (land, waits, rets), _ = run([E5(), K8()], stub)
    assert len(stub.calls) == 1, stub.calls          # the second batch reuses the result by text hashes


def test_fails_without_a_too_is_not_this_checks_verdict():
    fresh()
    (land, waits, rets), _ = run([E5(), K8()], Stub(with_="FAIL", without="FAIL"))
    assert [p["group"] for p in land] == ["E5", "K8"] and not waits and not rets


def test_not_decided_later_waits_then_pending_then_cap():
    fresh()
    t = [1000.0]
    now = lambda: t[0]
    stub = Stub(with_="NOT RUN")
    (land, waits, rets), _ = run([E5(), K8()], stub, now=now)
    assert [p["group"] for p in land] == ["E5"] and [p["group"] for p, _ in waits] == ["K8"], (land, waits)
    assert (bp.DIR / "pending" / ("k8" * 20 + ".json")).exists()
    # next batch: E5 is on main, K8 alone in its batch; the pending record still pairs it with E5's texts
    main2 = dict(MAIN, **{"Sheaf.ChainData": CHAIN_NEW})
    k8 = plan("K8", "Sheaf.KFlatFlat", "k8" * 20, KFLAT_OLD, KFLAT_NEW)
    stub2 = Stub(with_="FAIL", without="OK")
    (land, waits, rets), _ = run([k8], stub2, now=now, main=main2)
    assert not land and [p["group"] for p, _ in rets] == ["K8"], (land, waits, rets)
    assert stub2.calls and stub2.calls[0][0] == ["Sheaf.ChainData"]
    assert not (bp.DIR / "pending" / ("k8" * 20 + ".json")).exists()
    # cap: a pair still not decided after SHEAF_BATCH_PAIR_WAIT lands as before
    fresh()
    (land, waits, rets), _ = run([E5(), K8()], Stub(with_="NOT RUN"), now=now)
    t[0] += bp.WAIT + 1
    (land, waits, rets), _ = run([E5(), K8()], Stub(with_="NOT RUN"), now=now)
    assert [p["group"] for p in land] == ["E5", "K8"] and not waits, (land, waits)


def test_pending_dropped_when_a_not_on_main():
    fresh()
    t = [1000.0]
    run([E5(), K8()], Stub(with_="NOT RUN"), now=lambda: t[0])
    stub = Stub()
    (land, waits, rets), _ = run([K8()], stub, now=lambda: t[0])     # E5 taken out again: main has the old text
    assert [p["group"] for p in land] == ["K8"] and not stub.calls
    assert not (bp.DIR / "pending" / ("k8" * 20 + ".json")).exists()


def _prerun(plans, stub, main=MAIN):
    import time
    bp._PRE.update(sig=None, t=0.0)
    logs = []
    n = bp.prerun(plans, lambda: combined(plans, main), lambda *a: logs.append(" ".join(map(str, a))), compile=stub,
                  source=main.get)
    t_end = time.time() + 30
    while time.time() < t_end and bp._busy([bp.pair_key(bp.texts_of(a["D"]), bp.texts_of(b["D"])) for a in plans for b in plans]):
        time.sleep(0.05)
    return n, logs


def test_prerun_compiles_ahead_and_the_landing_reuses_it():
    fresh()
    pub = bp.published_commit
    bp.published_commit = lambda: "P1"
    try:
        stub = Stub(with_="OK")
        n, logs = _prerun([E5(), C1(), K8()], stub)
        assert n == 1 and len(stub.calls) == 1, (n, stub.calls, logs)
        assert "ahead of the landing" in logs[0], logs
        n2, _ = _prerun([E5(), C1(), K8()], stub)          # decided: nothing queued again
        assert n2 == 0 and len(stub.calls) == 1
        (land, waits, rets), _ = run([E5(), C1(), K8()], stub)
        assert [p["group"] for p in land] == ["E5", "C1", "K8"] and not waits and not rets
        assert len(stub.calls) == 1, stub.calls             # the landing compiled nothing
    finally:
        bp.published_commit = pub


def test_result_of_an_older_build_is_compiled_again_only_when_the_batch_touched_it():
    fresh()
    pub, chg = bp.published_commit, bp.changed_modules
    try:
        bp.published_commit = lambda: "P1"
        stub = Stub(with_="OK")
        _prerun([E5(), K8()], stub)
        assert len(stub.calls) == 1
        # the in-flight batch changed an unrelated module: the result stands
        bp.published_commit = lambda: "P2"
        bp.changed_modules = lambda a, b: {"Sheaf.Other"}
        (land, waits, rets), _ = run([E5(), K8()], stub)
        assert [p["group"] for p in land] == ["E5", "K8"] and len(stub.calls) == 1, stub.calls
        # it changed a module only K8's imports import (not K8 itself, not a direct import): the result stands
        bp.published_commit = lambda: "P2b"
        bp.changed_modules = lambda a, b: {"Sheaf.Base"}
        main_b = dict(MAIN, **{"Sheaf.Base": mod("theorem base : True := trivial\n")})
        main_b["Sheaf.ChainData"] = CHAIN_OLD.replace("\n\n@[expose]", "\npublic import Sheaf.Base\n\n@[expose]", 1)
        g = combined([E5(), K8()], main_b)
        g["Sheaf.ChainData"] = set(g.get("Sheaf.ChainData", ())) | {"Sheaf.Base"}
        assert not bp.stale({"pub": "P1"}, {"Sheaf.KFlatFlat"}, g, "P2b", {})
        assert bp.stale({"pub": "P1"}, {"Sheaf.ChainData"}, g, "P2b", {})
        # it changed a module K8 imports: compiled again against the new build
        bp.published_commit = lambda: "P3"
        bp.changed_modules = lambda a, b: {"Sheaf.ChainData"}
        (land, waits, rets), _ = run([E5(), K8()], stub)
        assert [p["group"] for p in land] == ["E5", "K8"] and len(stub.calls) == 2, stub.calls
        # git cannot tell: compiled again
        bp.published_commit = lambda: "P4"
        bp.changed_modules = lambda a, b: None
        bp._CHANGED.clear()
        run([E5(), K8()], stub)
        assert len(stub.calls) == 3, stub.calls
    finally:
        bp.published_commit, bp.changed_modules = pub, chg


if __name__ == "__main__":
    bad = 0
    for k, f in sorted(globals().items()):
        if k.startswith("test_") and callable(f):
            try:
                f(); print("ok  ", k)
            except AssertionError as e:
                bad += 1; print("FAIL", k, str(e)[:600])
    sys.exit(1 if bad else 0)
