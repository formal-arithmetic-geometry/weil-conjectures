/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedComparisonsCore
import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedComparisonsPullback

/-! # Localization of the normalized strict reindexing comparisons

We show that the strict reindexing comparisons along an isomorphism of schemes descend to
derived comparisons satisfying all localization laws.

## Implementation details

The core laws (reduction evaluation, limit projection, unit, finite and limit models) are proved
in `podReindexingDerivedComparisonsCore`; the `pullback` field is then replaced by the
normalized completed-pullback realization from `podReindexingDerivedComparisonsPullback`. The
derivation passes through sectionwise equivalences on integral and finite modules, the
normalized limit-to-Roos map on K-injective systems, and the universal property of
localization. No completeness or boundedness is used.

## References

* Stacks 03EL, 07A4, 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
  (SY : PodSignedRoosShift (scalarReductionSource l E Y))
  (SX : PodSignedRoosShift (scalarReductionSource l E X))

/-- Given strict reindexing data along `g` satisfying its laws and quotient comparisons `β`
normalized on generators and compatible with the quotient transitions, there are derived
reindexing comparisons satisfying all localization laws, including pullback normalization. -/
theorem podReindexingDerivedComparisons
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (S : PodReindexingStrictData l E g) (hS : S.Laws l E g SY SX)
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n ((isoReductionIntegralComplex l E g).obj P))
    (hβ : podReindexingQuotientGenerators l E g β)
    (htransition : podReindexingQuotientTransition l E g β)
    (CY : IntegralOnSlice.completion l E Y none ≅
      (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y)
    (CX : IntegralOnSlice.completion l E X none ≅
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X) :
    ∃ R : PodReindexingDerivedData l E g, R.Laws l E g SY SX S β CY CX := by
  obtain ⟨R, hR⟩ := podReindexingDerivedComparisonsCore l E g SY SX S hS β hβ
    htransition CY CX
  obtain ⟨hReduction, hProjection, hUnit, hFinite, hLimit⟩ := hR
  obtain ⟨p, hPullback⟩ := podReindexingDerivedComparisonsPullback l E g SY SX S β CY CX R
  -- The five core laws do not read the `pullback` field, so they survive its replacement.
  exact ⟨{ R with pullback := p }, hReduction, hProjection, hUnit, hFinite, hLimit, hPullback⟩

end WeilConjectures
