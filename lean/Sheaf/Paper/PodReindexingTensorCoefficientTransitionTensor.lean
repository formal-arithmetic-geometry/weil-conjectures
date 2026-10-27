/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.Paper.PodReindexingTensorCoefficientTransitionCore

/-! # Completed tensor square for scalar/reindexing transitions

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-reindexing-tensor-coefficient-transition-tensor).
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

/-- The normalized completed tensor square of a coefficient transition.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 03EL, 06YY, 0941
(blueprint: lem-pod-reindexing-tensor-coefficient-transition-tensor).

Proof: on simultaneous flat quotient resolutions, both routes send every
homogeneous pure tensor to the same scalar tensor by balanced associativity.
The formula commutes with quotient transitions and with the signed total
differential.  Applying the full Roos realization and the normalized tensor
comparisons gives the displayed derived equality for all constructible inputs.
-/
theorem podReindexingTensorCoefficientTransition_tensor
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S) :
    ∀ M N : sfIntegralConstructibleCategory l E Y,
      (integralOrdinaryDerivedScalar l E L ι X).map (T.tensor M N).hom ≫
        (scalarTensorOrdinary l E L ι X).hom.app
          ((podOrdinaryReindex l E g).obj M.obj, (podOrdinaryReindex l E g).obj N.obj) ≫
        (integralCompletedTensor l L X).map
          (Prod.mkHom ((S.derived l E L ι g D D').hom.app M.obj)
            ((S.derived l E L ι g D D').hom.app N.obj)) =
      (S.derived l E L ι g D D').hom.app
          ((integralCompletedTensor l E Y).obj (M.obj, N.obj)) ≫
        (podOrdinaryReindex l L g).map
          ((scalarTensorOrdinary l E L ι Y).hom.app (M.obj, N.obj)) ≫
        (T'.tensor ⟨_, S.sourceConstructible M⟩ ⟨_, S.sourceConstructible N⟩).hom := by
  sorry

end WeilConjectures
