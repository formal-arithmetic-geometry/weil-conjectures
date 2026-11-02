/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.SpTwistedPullback.TwistedPullbackReductionData
import all WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineRestrictions
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import WeilConjectures.SmoothPurity.CoefficientClosedStructure.CoefficientClosedTensorComparison
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated

/-! # Signed Tate tensor in the coefficient-calculus presentation

Source: blueprint integral-adjunction-bijection, Purity paragraph.
(blueprint: lem-sp-twisted-pullback-line-membership).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.SpTwistedPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Tensor with the signed degree-zero Tate line in the fixed integral closed model
preserves the intrinsic integral constructible predicate.
Source: blueprint integral-adjunction-bijection, Purity paragraph;
Bhatt--Scholze 3.4.12, 3.5.1, 6.5.9; Stacks 07A4.
(blueprint: lem-sp-twisted-pullback-line-membership).

Proof: the completed first Tate line is locally free of rank one and has finite
locally constant reductions. Apply integral_line_reduction_restriction to it.
The PreservesIntegral clause gives membership after ordinary derived tensor
with every signed power. Identify that ordinary tensor presentation with the
integral closed tensor in the coefficient calculus: on simultaneous K-flat
representatives both are the same total sheaf tensor. Their universal derived
comparison and the single-complex localization isomorphism give a natural
isomorphism between these two presentations. Its second factor identifies the
generic signed power with integralTwistLine, including the dual at negative
integers and the coefficient unit at zero. Transport membership through this
isomorphism by sfIntegralConstructible_isClosedUnderIsomorphisms. This changes
no input and requires neither boundedness of the ambient complex nor a choice
of a finite-field datum. -/
theorem twistedPullbackLineMembership (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (m : ℤ)
    (M : sfIntegralConstructibleCategory l E X) :
    sfIntegralConstructible l E X
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.integralClosed.tensor.obj
        (M.obj, (DerivedCategory.singleFunctor _ 0).obj (integralTwistLine l E X m))) := by
  let L := AlgebraicGeometry.Scheme.purTwistIntegralModule X l E
  have hL : L.IsFiniteLocallyFreeOfRank 1 :=
    (AlgebraicGeometry.Scheme.pur_twist_sheaf_locally_free.{u, u} X l E).2.2.1.2.2.1
  let := hL
  have h := (IntegralLineReduction.preserves_integral l E X
    (fun x ↦ inferInstance) L m M).1
  have hp : IntegralLineReduction.power l E X L m = integralTwistLine l E X m :=
    IntegralLineReduction.power_eq_coefficient l E X L m
  let S := @RingedSiteDualityModel.closed.{u + 1, u, u, u + 2}
    _ _ _ (IntegralOnSlice.abSheafify.{u, u} X none)
    (IntegralOnSlice.abLocallyBijective.{u, u} X none) _ _
    (IntegralOnSlice.duality.{u, u} l E X none)
  change sfIntegralConstructible l E X
    (S.tensor.obj (M.obj, (DerivedCategory.singleFunctor _ 0).obj
      (IntegralLineReduction.power l E X L m))) at h
  rw [hp] at h
  let a := CoefficientClosedStructure.comparison S
    (coefficientDerivedSystemEvaluationCalculus l E X).choose.integralClosed
  exact ObjectProperty.prop_of_iso (sfIntegralConstructible l E X)
    (a.app (M.obj, (DerivedCategory.singleFunctor _ 0).obj (integralTwistLine l E X m))) h

end WeilConjectures.SpTwistedPullback
