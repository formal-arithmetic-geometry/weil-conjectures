/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletionMateComparison
public import WeilConjectures.AlgebraicGeometry.CompleteCoefficientDatumSupplement

/-! # Direct-image reconstruction on small constant-coefficient sites

Source: Stacks 099N(3),(4), 0B56, 0941; fix-lem-exchanges Step 5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory.AdicSites

/-- The strict projection mate is invertible on complete inputs, and its derived limit
intertwines the prescribed completion units with the canonical direct-image/limit map.
Source: Stacks 099N(3),(4), 0B56, 0941; fix-lem-exchanges Step 5, direct-image letter.
(blueprint: lem-sf-cbc-small-site-direct-image-reconstruction)

Proof: identify each lifted quotient with ULift of the original quotient by the ring
isomorphism induced by ULift.ringEquiv. Perfectness is transported by this scalar
isomorphism. The perfect projection formula makes each evaluated counit-tensor mate
invertible. Derived strict-tower cohomology is levelwise, so its cone is zero and the
whole tower mate is invertible. For normalization, first identify constant pullback
with pullback of constant towers by the identity component comparison. Conjugating
this comparison through the constant/limit and pullback/pushforward adjunctions gives
exactly directLimitIso, including its normalization at constant towers. The quotient
augmentation is compatible with tensor pullback. Its adjunction mate thus satisfies
the augmentation square h i = towerPush(i) chi. Apply the derived limit and its
constant-tower normalization; naturality of directLimitIso gives the displayed unit
equation. All these equations hold in derived strict towers before evaluation.
This argument includes zero and unit ideals, the zero ring, and empty sites; no
uniform Tor interval or bound on the input complex is used. -/
theorem smallSiteDirectImageReconstruction
    {V U : Site.{t + 1}} (f : Morphism V U)
    {A : Type t} [CommRing A] (d : AlgebraicGeometry.Scheme.CompleteCoefficientDatum A)
    (K : U.derived (ULift.{t + 1, t} A))
    (hK : U.IsComplete _ (d.ideal.map ULift.ringEquiv.symm.toRingHom) K) :
    let I := d.ideal.map ULift.ringEquiv.symm.toRingHom
    IsIso (f.towerProjection (ULift.{t + 1, t} A) I K) ∧
      (V.unit _ I).app ((f.push _).obj K) ≫
          (V.rlim _).map (f.towerProjection _ I K) =
        (f.push _).map ((U.unit _ I).app K) ≫
          (f.directLimitIso _).hom.app ((U.reduction _ I).obj K) := by sorry

end CategoryTheory.AdicSites
