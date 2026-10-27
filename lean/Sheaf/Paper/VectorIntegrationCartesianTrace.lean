/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.VectorPurityBaseChange

/-! # Integration traces in arbitrary Cartesian bundle presentations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The scalar integration trace is preserved in every Cartesian presentation.
Source: latest blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2, equality of integrations before transposition.
(blueprint: lem-pur-vector-integration-cartesian-trace).

Proof: first use vectorBundleIntegration_baseChange for the canonical tensor-pullback bundle.
The universal property of the two Cartesian squares identifies any other presentation with
that bundle over the new base. The top compact-support trace is invariant under this
isomorphism: on each geometric fibre it is the degree map on top compact-support cohomology,
and an isomorphism has degree one. Both trace sources are degree-zero sheaves, so geometric
stalks detect their equality. The normalized Tate pullback comparison and the composition
comparisons identify the coefficient map with the displayed one. Compact-support exchange
pastes with the presentation isomorphism, giving the formula. Finally the canonical map
from the degree-zero constant coefficient to the tensor unit commutes with pullback.
For rank zero these are unit comparisons; over an empty base there is only one map.
This statement contains no exceptional inverse image or purity family.
-/
theorem vectorIntegration_cartesianTrace
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {B B' : Scheme.{u}} [IsNoetherian B] [IsNoetherian B']
    (hB : IsUnit (N : Γ(B, ⊤))) (hB' : IsUnit (N : Γ(B', ⊤)))
    (d : ℕ) (F : B.Modules) (F' : B'.Modules)
    [F.IsFiniteLocallyFreeOfRank d] [F'.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    [HasCompactification (VectorBundleZeroSection.π B' d F')]
    [QuasiCompact (VectorBundleZeroSection.π B' d F')]
    {g : B' ⟶ B}
    {g' : VectorBundleZeroSection.scheme B' d F' ⟶ VectorBundleZeroSection.scheme B d F}
    (sq : IsPullback g' (VectorBundleZeroSection.π B' d F')
      (VectorBundleZeroSection.π B d F) g) :
    let l := purityPullbackSquare A sq (Etale.affineLinearBaseCoefficient A N hA B d) ≪≫
      (RfPullback A (VectorBundleZeroSection.π B' d F')).mapIso
        (Etale.vectorIntegrationBaseCoefficientPullback A N hA
          (purityTwistTransport A N hN hA) g hB d)
    (Etale.rightDerivedLowerShriekBaseChangeMap A sq).app
        (Etale.vectorIntegrationCoefficient A N hA B d F) ≫
      (RfShriek A (VectorBundleZeroSection.π B' d F')).map l.hom ≫
      (Etale.vectorBundleIntegration N hN A hA B' hB' d F' ≫
        (Etale.singleFunctorObjUnitIso (ModuleCat A) B').hom) =
    (RfPullback A g).map (Etale.vectorBundleIntegration N hN A hA B hB d F ≫
      (Etale.singleFunctorObjUnitIso (ModuleCat A) B).hom) ≫
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat A) g).hom := by sorry

end WeilConjectures.PurityFiniteSetting
