# AlgebraicGeometry.Scheme.finite_ctf_isTriangulated

## Reason

The proof uses the zero-object notation and monoidal tensor notation. It adds
`open scoped ZeroObject` and `open CategoryTheory.MonoidalCategory` to this module.
The static interface checker requires a change record for these commands. They only make
existing notation and names available while elaborating this file; no definition, target
statement, existing signature or visibility is changed. All new helper declarations are
private and proved, and the instance-size option is scoped to the private tensor proof.

## Old

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

theorem finite_ctf_isTriangulated
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E n hn Y ⊓
        fun K ↦ HasFiniteProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) K) ∧
    ObjectProperty.IsTriangulated
      (intrinsicFiniteTorsionConstructible l E n hn Y ⊓
        fun K ↦ HasFiniteProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) K) ∧
    (∀ (K : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)) (a b m : ℤ),
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) K a b →
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n)
        (K⟦m⟧) (a - m) (b - m)) ∧
    (∀ (T : Triangle (proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)))
      (a b : ℤ), T ∈ distTriang _ →
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) T.obj₁ a b →
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) T.obj₃ a b →
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) T.obj₂ a b)
```

## New

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
open CategoryTheory.MonoidalCategory

theorem finite_ctf_isTriangulated
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E n hn Y ⊓
        fun K ↦ HasFiniteProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) K) ∧
    ObjectProperty.IsTriangulated
      (intrinsicFiniteTorsionConstructible l E n hn Y ⊓
        fun K ↦ HasFiniteProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) K) ∧
    (∀ (K : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)) (a b m : ℤ),
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) K a b →
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n)
        (K⟦m⟧) (a - m) (b - m)) ∧
    (∀ (T : Triangle (proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)))
      (a b : ℤ), T ∈ distTriang _ →
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) T.obj₁ a b →
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) T.obj₃ a b →
      HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E n) T.obj₂ a b)
```

The theorem's proof is filled. The two added proof imports are private imports, including
`import all Sheaf.Algebra.Homology.KFlatResolutionGeneral` to use its existing proved internal
constructions. The unused valued-field proof import is removed. No public definition body
contains private data, and the public theorem statement mentions none of the private helpers.

## Users

`tools/downstream.py Sheaf.Paper.FiniteCtfTriangulated --uses
AlgebraicGeometry.Scheme.finite_ctf_isTriangulated` reports zero downstream modules and only the
declaration's own occurrence. No consumer requires adaptation. This is compatible with stage 3
opening a declared dependency before its parent's proof imports it.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteCtfTriangulated | G1 | Complete proof; existing signature and meaning unchanged. |

## Status

landed 20261018T062756-L-650780 2026-10-18 (merge of deliver/G1/Sheaf.Paper.FiniteCtfTriangulated)
