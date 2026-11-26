/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.TraceFormula.Supporting.RoosAdjunctionQuotientNormalization
public import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientRealizationComparisons
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.Isomorphism.IsomorphismDerivedPullbackComparisonNormalization
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import WeilConjectures.TraceFormula.Supporting.TransportedReductionSystemsNormalized
import WeilConjectures.TraceFormula.Primitive.PrimitiveQuotientRealizationsUnique
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic
import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined

/-! # Effectivity and simultaneous descent of quotient realization models

We record the ambient normalization, the reconstruction maps and the primitive normalized
models for the completed pullback and scalar extension
(`WeilConjectures.effectiveQuotientModelDescent`), and the bounded constructibility of both
completed operations and their system realizations
(`WeilConjectures.effectiveQuotientModelConstructible`).

The ambient assertions keep independent site and coefficient universes. In the
constructibility assertion, u is a common bound for schemes and coefficient fields,
as in the recorded intrinsic constructibility predicate. The small site still has
objects in Type (u+1) and morphisms in Type u. Level n means exponent n+1.

## Implementation details

For `WeilConjectures.effectiveQuotientModelDescent`:
1. The evaluation calculus makes every reduction normalized, and exact whole-system inverse image
   preserves its transition adjoints.
2. Scalar change of the same strict reduction diagram is identified with its normalized scalar
   quotient model; balanced association commutes with every quotient map, even for ramified
   extensions.
3. Normalized reconstruction, applied to both normalized systems, gives completeness and
   invertibility of the whole-system counits, and invertibility of the unit for complete inputs,
   without any bounds.
4. `primitiveQuotientRealizationComparisons` gives the two natural models for these functors and
   the fixed Roos comparisons, normalized on every K-flat presentation; the counit is identified
   with the K-injective projections and the unit with the zero-shifted quotient augmentation, so
   the maps are the specified adjunction maps.

For `WeilConjectures.effectiveQuotientModelConstructible`, the preservation of constructibility
by the integral operations (`integralOperations_preserve_constructible`) and by integral scalar
extension is transported through the primitive comparison isomorphisms; completeness,
constructible reductions and their common finite interval are invariant under these
isomorphisms, and no bound on the quotient ring map is needed.

## References

* [Stacks: Tags 0941, 06YS, 07A4, 099N]
* [B. Bhatt, P. Scholze, *The pro-étale topology for schemes*, Lemmas 6.5.4 and 6.5.9(5)]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

attribute [local irreducible] WeilConjectures.integralComparisonSequenceScalarModel
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.standard CategoryTheory.constantSheaf
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.coefficientSequenceLimit
  WeilConjectures.integralOperationsRoosFunctor WeilConjectures.integralOperationsGoodLocalization
  WeilConjectures.sfIntegralConstructible

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Ambient normalization, actual reconstruction maps, and primitive normalized models. -/
-- STATEMENT-DISPUTED: inherits the universal-presentation normalization obstruction of
-- primitiveQuotientRealizationComparisons; finite derived evaluations do not fix the
-- whole-system presentation isomorphism. See the report and the existing T6 counterexample.
theorem effectiveQuotientModelDescent
    {X Y : Scheme.{t}} (f : X ⟶ Y)
    (_hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hlY : ∀ y : Y, IsUnit (l : Y.residueField y))
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SL : CoefficientDerivedSystemCalculus l L Y)
    (ρX : IntegralComparisonRoosModel l E X)
    (ρL : IntegralComparisonRoosModel l L Y) :
    (∀ K : DerivedCategory (scalarReductionSource l E Y),
      IsNormalizedCoefficientSequence l E Y (SY.reduction.obj K) ∧
      IsNormalizedCoefficientSequence l E X
        ((integralComparisonDerivedSequencePullback l E f).obj (SY.reduction.obj K)) ∧
      IsNormalizedCoefficientSequence l L Y
        ((integralComparisonDerivedSequenceScalar l E L ι Y).obj (SY.reduction.obj K)) ∧
      IntegralOnSlice.IsComplete l E X none ((coefficientSequenceLimit l E X).obj
        ((integralComparisonDerivedSequencePullback l E f).obj (SY.reduction.obj K))) ∧
      IntegralOnSlice.IsComplete l L Y none ((coefficientSequenceLimit l L Y).obj
        ((integralComparisonDerivedSequenceScalar l E L ι Y).obj (SY.reduction.obj K))) ∧
      IsIso (SX.adjunction.counit.app
        ((integralComparisonDerivedSequencePullback l E f).obj (SY.reduction.obj K))) ∧
      IsIso (SL.adjunction.counit.app
        ((integralComparisonDerivedSequenceScalar l E L ι Y).obj (SY.reduction.obj K))) ∧
      (IntegralOnSlice.IsComplete l E Y none K → IsIso (SY.adjunction.unit.app K))) ∧
    Nonempty (IntegralComparisonPullbackModel l E f SY ρX) ∧
    Nonempty (IntegralComparisonScalarModel l E L ι Y SY ρL) := by
  obtain ⟨hnp, hns⟩ := transportedReductionSystems_normalized l E L ι f _hlX _hlY SY
  obtain ⟨hp, hs⟩ := primitiveQuotientRealizationComparisons l E L ι f Y
    _hlX _hlY _hlY SY SY ρX ρL
  refine ⟨fun K ↦ ?_, hp, hs⟩
  have hx := (purNormalizedReconstructionOfScheme l E X SX).1 _ (hnp K)
  have hl := (purNormalizedReconstructionOfScheme l L Y SL).1 _ (hns K)
  exact ⟨SY.reduction_normalized K, hnp K, hns K, hx.1, hl.1, hx.2, hl.2,
    (purNormalizedReconstructionOfScheme l E Y SY).2 K⟩

/-- Bounded constructibility, with one interval for all reductions, is retained by
both completed operations and their specified system realizations. -/
theorem effectiveQuotientModelConstructible
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (SY : CoefficientDerivedSystemCalculus l E Y)
    (ρX : IntegralComparisonRoosModel l E X)
    (ρL : IntegralComparisonRoosModel l L Y)
    (α : IntegralComparisonPullbackModel l E f SY ρX)
    (β : IntegralComparisonScalarModel l E L ι Y SY ρL)
    (K : DerivedCategory (scalarReductionSource l E Y))
    (_hK : sfIntegralConstructible l E Y K) :
    sfIntegralConstructible l E X ((integralDerivedPullback l E f).obj K) ∧
    sfIntegralConstructible l L Y ((integralScalarExtensionOfUniverses l E L ι Y).obj K) ∧
    sfIntegralConstructible l E X ((coefficientSequenceLimit l E X).obj
      ((integralComparisonDerivedSequencePullback l E f).obj (SY.reduction.obj K))) ∧
    sfIntegralConstructible l L Y ((coefficientSequenceLimit l L Y).obj
      ((integralComparisonDerivedSequenceScalar l E L ι Y).obj (SY.reduction.obj K))) := by
  have hp := ((integralOperations_preserve_constructible l E f).1 K _hK).1
  have hs : sfIntegralConstructible l L Y
      ((integralScalarExtensionOfUniverses l E L ι Y).obj K) :=
    sfIntegralScalarExtension_constructible (l + 1) l (by omega) E L ι Y K _hK
  exact ⟨hp, hs,
    (sfIntegralConstructible l E X).prop_of_iso (α.realization.app K) hp,
    (sfIntegralConstructible l L Y).prop_of_iso (β.realization.app K) hs⟩

section RoosComparisonUniqueness

-- The computes field uses the defining Roos object, so keep this comparison transparent.
attribute [local semireducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
  completedIntegralCoefficientSheafUnrestricted coefficientSequenceLimit
  integralOperationsRoosFunctor integralOperationsGoodLocalization sfIntegralConstructible

end RoosComparisonUniqueness

universe sa sb sw

section ScalarData
open SheafOfModules
variable {C₀ : Type sa} [Category.{sb} C₀] {J : GrothendieckTopology C₀}
  [J.HasSheafCompose (forget₂ CommRingCat.{sw} RingCat.{sw})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{sw}] [HasSheafify J AddCommGrpCat.{sw}]
  [EssentiallySmall.{sw} C₀]

end ScalarData

end WeilConjectures
