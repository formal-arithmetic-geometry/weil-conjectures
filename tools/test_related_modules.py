#!/usr/bin/env python3
"""Tests of tools/related_modules.py on small synthetic module graphs (no Lean, no repository data)."""
import pathlib, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import related_modules as rm  # noqa: E402

HDR = "module\n\npublic import Mathlib\n\n@[expose] public section\n\nnamespace Foo\n\n"


def mod(body: str, imports=()) -> str:
    return "module\n\n" + "".join(f"public import {i}\n" for i in imports) + "\n@[expose] public section\n\nnamespace Foo\n\n" + body + "\nend Foo\n"


def run(changes, texts, cap=150):
    imports = rm.graph_of_texts(texts)
    return rm.related(changes, rm.with_new_texts(imports, changes), texts.get, cap)


def test_proof_only_has_no_related():
    old = mod("theorem a : 1 = 1 := by\n  rfl\n")
    new = mod("theorem a : 1 = 1 := by\n  simp\n")
    texts = {"A": old, "B": mod("theorem b : 1 = 1 := a\n", ["A"]), "C": mod("theorem c := a\n", ["B"])}
    r = run({"A": (old, new)}, texts)
    assert r["related"] == [], r


def test_statement_change_direct_and_mentioning_transitive():
    old = mod("theorem alphaLemma : 1 = 1 := by\n  rfl\n")
    new = mod("theorem alphaLemma : 2 = 2 := by\n  rfl\n")
    texts = {"A": old, "B": mod("theorem b : True := trivial\n", ["A"]),
             "C": mod("theorem c : 1 = 1 := alphaLemma\n", ["B"]),
             "D": mod("theorem d : True := trivial\n", ["B"]),
             "E": mod("-- alphaLemma in a comment only\ntheorem e : True := trivial\n", ["C"])}
    r = run({"A": (old, new)}, texts)
    assert sorted(r["direct"]) == ["B"], r
    assert [x["module"] for x in r["transitive"]] == ["C"], r
    assert r["related"] == ["B", "C"]


def test_removed_instance_selects_class_mentions():
    old = mod("instance fooAdd : AddCommGroup Nat := sorry\ninstance shortcutAdditive : Functor.Additive F := sorry\n")
    new = mod("instance fooAdd : AddCommGroup Nat := sorry\n")
    texts = {"A": old, "B": mod("theorem b : True := trivial\n", ["A"]),
             "C": mod("theorem c (h : (G).Additive) : True := trivial\n", ["B"]),
             "D": mod("theorem d : True := trivial\n", ["B"])}
    r = run({"A": (old, new)}, texts)
    assert "Additive" in r["classes"], r
    assert [x["module"] for x in r["transitive"]] == ["C"], r


def test_added_instance_needs_class_and_constant():
    old = mod("def fooMap : Nat := 1\n")
    new = mod("def fooMap : Nat := 1\ninstance fooMap_isIso : IsIso (fooMapping X) := sorry\n")
    texts = {"A": old, "B": mod("theorem b : True := trivial\n", ["A"]),
             "C": mod("theorem c [IsIso f] : True := trivial\n", ["B"]),
             "D": mod("theorem d [IsIso (fooMapping Y)] : True := trivial\n", ["B"])}
    r = run({"A": (old, new)}, texts)
    assert [x["module"] for x in r["transitive"]] == ["D"], r


def test_class_of_dotted_conclusion():
    assert rm.classes_of("(Z : Scheme) : ∀ (X Y : C), (coherentTopology Profinite).W.IsMonoidal") == {"IsMonoidal"}
    assert rm.classes_of(": (f)^*⟦Λ⟧.Additive") == {"Additive"}
    assert rm.classes_of("(Z : Scheme.{u}) : MonoidalCategory (CochainComplex (Mod Z) ℤ)") == {"MonoidalCategory"}


def test_local_attribute_is_not_relevant():
    old = mod("theorem x : True := trivial\n")
    new = mod("attribute [local instance] fooInst\ntheorem x : True := trivial\n")
    assert rm.instance_classes(old, new)[0] == set()
    new2 = mod("attribute [instance] fooInst\ntheorem x : True := trivial\n")
    assert rm.instance_classes(old, new2)[0] == {"fooInst"}


def test_cap_nearest_first():
    old = mod("theorem betaLemma : 1 = 1 := rfl\n")
    new = mod("theorem betaLemma : 2 = 2 := rfl\n")
    texts = {"A": old, "B": mod("theorem b : True := trivial\n", ["A"]),
             "C2": mod("theorem c := betaLemma\n", ["B"]), "C3": mod("theorem c := betaLemma\n", ["C2"]),
             "C4": mod("theorem c := betaLemma\n", ["C3"])}
    r = run({"A": (old, new)}, texts, cap=2)
    assert [x["module"] for x in r["transitive"]] == ["C2", "C3"] and r["capped"] and r["left_out"] == ["C4"], r


def test_new_module_names_reach_importers_of_its_importer():
    old = mod("theorem a : True := trivial\n")
    new = mod("theorem a : True := trivial\n", ["N"])
    newmod = mod("theorem gammaClash : True := trivial\n")
    texts = {"A": old, "B": mod("theorem b : True := trivial\n", ["A"]),
             "C": mod("theorem gammaClash : True := trivial\n", ["B"])}
    r = run({"A": (old, new), "N": (None, newmod)}, texts)
    assert sorted(r["direct"]) == ["B"] and [x["module"] for x in r["transitive"]] == ["C"], r


if __name__ == "__main__":
    bad = 0
    for k, f in sorted(globals().items()):
        if k.startswith("test_") and callable(f):
            try:
                f(); print("ok  ", k)
            except AssertionError as e:
                bad += 1; print("FAIL", k, str(e)[:600])
    sys.exit(1 if bad else 0)
