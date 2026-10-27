# AlgebraicGeometry.Etale.isIso_projectionMap_coefficientExtensionRing

## Reason

Complete the existing theorem by specializing the proved
`sf_finite_etale_projection_formula` at the existing Nagata compactification.
The local instance priority and local irreducibility attributes match the proof
context of that theorem and prevent expensive expansion of derived projection
bifunctors during elaboration. They have no exported effect. Public imports,
all declaration signatures and the compactification definition remain verbatim.

## Old

```lean
theorem isIso_projectionMap_coefficientExtensionRing
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (L : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Y)
    (_hKc : ∀ i : ℤ, Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)))).obj
        ((_root_.DerivedCategory.homologyFunctor _ i).obj K)))
    (_hKb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K))
    (_hLc : ∀ i : ℤ, Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)))).obj
        ((_root_.DerivedCategory.homologyFunctor _ i).obj L)))
    (_hLb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj L))
    (_hLt : ∃ a b : ℤ, a ≤ b ∧
      DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) Y a b L) :
    _root_.DerivedCategory.TStructure.t.plus
      (((derivedTensorRightDerivedLowerShriek
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
        (finiteCoefficientProjectionCompactification D f)).obj K).obj L) ∧
    _root_.DerivedCategory.TStructure.t.plus
      (((rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
        (finiteCoefficientProjectionCompactification D f)).obj K).obj L) ∧
    IsIso (((projectionMapOfCompactification
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
      (finiteCoefficientProjectionCompactification D f)).app K).app L) := by
  sorry
```

## New

```lean
theorem isIso_projectionMap_coefficientExtensionRing
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (L : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Y)
    (_hKc : ∀ i : ℤ, Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)))).obj
        ((_root_.DerivedCategory.homologyFunctor _ i).obj K)))
    (_hKb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K))
    (_hLc : ∀ i : ℤ, Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)))).obj
        ((_root_.DerivedCategory.homologyFunctor _ i).obj L)))
    (_hLb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj L))
    (_hLt : ∃ a b : ℤ, a ≤ b ∧
      DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) Y a b L) :
    _root_.DerivedCategory.TStructure.t.plus
      (((derivedTensorRightDerivedLowerShriek
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
        (finiteCoefficientProjectionCompactification D f)).obj K).obj L) ∧
    _root_.DerivedCategory.TStructure.t.plus
      (((rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
        (finiteCoefficientProjectionCompactification D f)).obj K).obj L) ∧
    IsIso (((projectionMapOfCompactification
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
      (finiteCoefficientProjectionCompactification D f)).app K).app L) := by
  obtain ⟨a, b, _hab, hTor⟩ := _hLt
  exact sf_finite_etale_projection_formula l E n _hn f
    (finiteCoefficientProjectionCompactification D f) K L _hKc _hKb _hLc _hLb
    ⟨a, b, hTor⟩
```

The added proof context is:

```lean
attribute [local instance 2000] CommRing.toRing
attribute [local irreducible] projectionMapOfCompactification
  derivedTensorRightDerivedLowerShriek rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
```

The local attributes affect elaboration in this file only. The new import
`Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula` is private. No statement,
definition, public instance or exported attribute changes.

## Users

`tools/downstream.py` lists one downstream module, `Sheaf.Paper.ProjectionFiniteReduction`.
The `--uses AlgebraicGeometry.Etale.isIso_projectionMap_coefficientExtensionRing`
search finds no external textual use. That consumer currently has a sorry proof and
imports this module as its planned dependency. Its statement and all referenced
definitions keep the same meaning; no consumer adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteCoefficientEtaleProjectionFormula | V1 | Same public interface; theorem proved using local elaboration attributes. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Same imported interface and meaning; no adaptation. |

No target statement or definition changes meaning, so target statement review does
not reopen.

## Status

landed 20261022T144315-L-1580722 2026-10-22 (merge of deliver/V1/Sheaf.AlgebraicGeometry.FiniteCoefficientEtaleProjectionFormula)
