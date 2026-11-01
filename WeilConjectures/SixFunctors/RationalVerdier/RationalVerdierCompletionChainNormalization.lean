/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
public import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionChain
import WeilConjectures.SixFunctors.OpenFactorCoherence.TensorCompletionChainUniqueness
import WeilConjectures.SixFunctors.OpenFactorCoherence.TensorOperationUnitNormalization

/-! # Identification of the chosen normalized tensor augmentation

Source: Bhatt--Scholze 3.4.10, 6.5.5; uniqueness from both Roos coordinates.
(blueprint: lem-coef-rational-verdier-completion-chain-normalization). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalVerdier

attribute [local implicit_reducible] integralOperationsGoodLocalization
  integralOperationsTensorOnGood integralOperationsTensorComplexFunctor
  IntegralAmbient.tensorTower
  IntegralOnSlice.Site IntegralOnSlice.topology IntegralOnSlice.restrict IntegralOnSlice.ring
  PurCompactSupport.completed
attribute [local irreducible] IntegralOnSlice.roosUnit IntegralAmbient.tensorTowerIso
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOperationsTensorTowerFunctor

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))] in
/-- The chosen completion map is the existing Roos augmentation with normalized
strict tensor comparison. Source: Bhatt--Scholze 3.4.10, 6.5.5.
(blueprint: lem-coef-rational-verdier-completion-chain-normalization).
Proof: extract the pure quotient and zero shifted coordinates from the chosen
witness, use the existing coordinate normalization of tensorOperationUnit for
the native map, and apply the existing two-coordinate uniqueness theorem. -/
theorem completionChain_eq_native :
    completionChain D l hl X E = ConstructibleTensorModel.tensorCompletionChain l E X := by
  apply OpenFactorCoherence.tensorCompletionChain_unique l E X
  · have h := (third_exists_first (@constructibleTensorCompletion l _ E _ _ _ X
      (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)))
      (quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of D.k)))
      (units D l hl X))).choose_spec
    obtain ⟨T, e, hf, hz, rest⟩ := h
    unfold completionChain
    exact ⟨hf, hz⟩
  · apply OpenFactorCoherence.tensorOperationUnit_normalized l E X
    intro P Q
    rw [ConstructibleTensorModel.tensorCompletionChain_app]
    unfold ConstructibleTensorModel.tensorCompletionUnitMap
    rfl

end WeilConjectures.RationalVerdier
