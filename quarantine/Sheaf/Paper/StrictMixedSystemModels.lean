/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.Paper.StrictDirectImageMixedUnitData

/-! # Normalized models for strict mixed reduction

Source: Stacks Tag 0B56, equation-projection-formula-map.
(blueprint: lem-weil-strict-mixed-system-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived

universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.StrictDirectImageMixedUnit
open SfStrictDirectImageScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Normalized reconstruction, restriction, and scalar models on the ringed sequence sites.
Source: Stacks 0D6E, 0A07, 07A6; Steps 1--3 of the strict mixed-unit calculation
(blueprint: lem-weil-strict-mixed-system-models).

Proof: construct the restriction/direct-image square by comparing the two factorizations
of the same ringed-topos map. Its ordinary map is identity on sections. Derive using
K-injective resolutions and the universal derived units. The conjugate pullback square
and system transposition identify its finite evaluation with finiteRestriction. Construct
CE and CL from the sectionwise limit/direct-image comparison, whose projections are the
limit projections; derive this comparison using the normalized right-derived compositor.
Choose the actual reduction/limit calculi and their coherence. Transpose reconstruction
through these adjunctions. The counit projection formula identifies the resulting maps
with finiteReduction and the projections of the strict Roos model. Proper direct-image
constructibility makes these reductions invertible; joint conservativity of evaluations
makes the system maps invertible. Construct AX, AY and dX, dY by the coefficient extension
reduction model. On a flat-term K-flat representative the mixed units send x to
(x tensor 1) tensor 1. Scalar association multiplies the two scalars, and the completion
augmentation has zero shifted Roos coordinate. The reduction/limit triangle therefore
identifies their finite evaluations with sfMixedCompletedReductionUnit. All constructions
are on entire sequence sites and retain the quotient transitions. No equality of arbitrary
system morphisms is inferred from finite evaluation. -/
theorem strictMixedSystemModels
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    (I : IntegralModel l E f) (J : IntegralModel l L f) :
  ∃ (EX : CoefficientDerivedSystemCalculus l E X),
  ∃ (EY : CoefficientDerivedSystemCalculus l E Y),
  ∃ (LX : CoefficientDerivedSystemCalculus l L X),
  ∃ (LY : CoefficientDerivedSystemCalculus l L Y),
  ∃ (AX : CoefficientExtensionSystems l E L ι X),
  ∃ (AY : CoefficientExtensionSystems l E L ι Y),
  ∃ (dX : CoefficientExtensionReductionData l E L ι X EX LX AX),
  ∃ (dY : CoefficientExtensionReductionData l E L ι Y EY LY AY),
  ∃ (CE : LimitComparison l E f),
  ∃ (CL : LimitComparison l L f),
  ∃ (restrictionComparison : RestrictionComparison l E L ι f),
  Nonempty (CoefficientDerivedSystemCoherence l E X EX) ∧
  Nonempty (CoefficientDerivedSystemCoherence l E Y EY) ∧
  Nonempty (CoefficientDerivedSystemCoherence l L X LX) ∧
  Nonempty (CoefficientDerivedSystemCoherence l L Y LY) ∧
  (StrictProjections l E f I) ∧
  (StrictProjections l L f J) ∧
  (RestrictionEvaluation l E L ι f restrictionComparison) ∧
  (ReductionEvaluation l E f EX EY CE I) ∧
  (ReductionEvaluation l L f LX LY CL J) ∧
  (MixedEvaluation l E L ι X EX LX AX dX) ∧
  (MixedEvaluation l E L ι Y EY LY AY dY) ∧
  (∀ K : sfIntegralConstructibleCategory l E X,
    IsIso (reductionMap l E f EX EY CE I K)) ∧
  (∀ K : sfIntegralConstructibleCategory l L X,
    IsIso (reductionMap l L f LX LY CL J K)) := by sorry

attribute [instance 20000] WeilConjectures.CompletedCoefficientPushforward.modAbelian
attribute [instance 10000] WeilConjectures.CompletedCoefficientPushforward.hasDerived

end WeilConjectures.StrictDirectImageMixedUnit
