# AlgebraicGeometry.Etale.sf_finite_etale_projection_formula

## Reason

Record the proof context commands that trigger the interface gate: `universe u` becomes
`universe u v`, and `open CategoryTheory CategoryTheory.Limits` also opens `MonoidalCategory`.
The extra universe supports private generic tensor helpers. The open command enables tensor
and braiding notation in their proofs. A local instance priority selects `CommRing.toRing`;
local irreducibility attributes prevent expansion of total tensor and projection definitions.
Each transparency option is scoped to its following theorem. These commands do not change
the exported theorem type, definitions, instances, or public imports. Every new helper is
private and completely proved; no other module is modified.

## Old

```lean
theorem sf_finite_etale_projection_formula
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
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
    (_hLt : ∃ a b : ℤ,
      DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) Y a b L) :
    _root_.DerivedCategory.TStructure.t.plus
      (((derivedTensorRightDerivedLowerShriek
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c).obj K).obj L) ∧
    _root_.DerivedCategory.TStructure.t.plus
      (((rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c).obj K).obj L) ∧
    IsIso (((sfEtaleProjection (Padic.coefficientExtensionRing l E n) c).app K).app L)
```

The old proof is `by sorry`. Its context declares only universe `u` and opens
`CategoryTheory CategoryTheory.Limits`.

## New

```lean
theorem sf_finite_etale_projection_formula
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
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
    (_hLt : ∃ a b : ℤ,
      DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) Y a b L) :
    _root_.DerivedCategory.TStructure.t.plus
      (((derivedTensorRightDerivedLowerShriek
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c).obj K).obj L) ∧
    _root_.DerivedCategory.TStructure.t.plus
      (((rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c).obj K).obj L) ∧
    IsIso (((sfEtaleProjection (Padic.coefficientExtensionRing l E n) c).app K).app L)
```

The signature is identical. Its proof now applies the finite-coefficient proper projection
formula, proves the lower tensor bound, and transports it across the canonical projection.
The added proof context is:

```lean
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance 2000] CommRing.toRing
attribute [local irreducible] HomologicalComplex₂.total
  projectionMapOfCompactification rightDerivedLowerStarProjectionMap
  derivedTensorRightDerivedLowerShriek rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerStar rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
```

The per-theorem command `set_option backward.isDefEq.respectTransparency false in` affects
elaboration only. All listed attributes are local. No new exported attribute is introduced.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula
--uses AlgebraicGeometry.Etale.sf_finite_etale_projection_formula` reports zero downstream
modules and only the declaration in the item itself as a textual use. A source search agrees.
No consumer adaptation is needed, and no target statement or definition changes meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | R9 | Same public theorem type and public imports; proof completed; local proof commands only. |

## Status

landed 20261021T194242-L-1516806 2026-10-21 (merge of deliver/R9/Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula)
