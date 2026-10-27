/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q5
-/
module

public import Sheaf.Paper.IntegralPullbackStrictRoosData

/-! Finite quotient augmentation compatibility for the balanced pullback comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.pbcIntegralDatum AlgebraicGeometry.Scheme.completedAdicChangeData
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralPullbackStrictRoos
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Balanced lambda preserves the ordinary quotient augmentation at each finite level.
Source: the integral tensor-pullback proof, first paragraph, strict refinement step 5;
Stacks Tags 03EK and 07A4.
(blueprint: lem-sfb-integral-lambda-quotient-augmentation).

Proof: test the two module maps on scalar-extension generators. The quotient
augmentation sends h to h tensor 1. The normalization of lambda sends the inverse
image of this generator to the tensor of the inverse image of h with the transported
unit residue. The coefficient homomorphism preserves 1, so this is the augmentation
of the pulled module. The pullback adjunction and the sheafified tensor universal
property imply equality from these generator identities. This works for arbitrary
modules, including torsion modules; no flatness or completeness is used. -/
theorem integralLambdaQuotientAugmentation
    (a : T l E g ≅ U l E g) (ha : IsLambdaNormalized l E g a)
    (M : ModR l E Y) (n : ℕ) :
    (pullR l E g).map
        (((completedReductionModuleUnit (datum l E) Y).app M).app (op n)) ≫
        (a.hom.app M).app (op n) =
      ((completedReductionModuleUnit (datum l E) X).app ((pullR l E g).obj M)).app
        (op n) := by sorry

end WeilConjectures.IntegralPullbackStrictRoos
