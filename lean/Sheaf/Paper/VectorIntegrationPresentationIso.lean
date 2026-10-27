/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.VectorBundleIntegration
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-! # Integration under an isomorphism of bundle presentations over a fixed base -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Integration is invariant under an arbitrary isomorphism of total spaces over one base.
Source: latest blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2, degree-zero descent of scalar traces;
lem-pur-vector-integration-cartesian-trace, proof step 2.
(blueprint: lem-pur-vector-integration-presentation-iso).

Proof: choose simultaneous frame opens for the two bundles. The given isomorphism,
restricted to each open and then to a geometric fibre, identifies two affine d-spaces.
The ordered affine trace sends the class of a rational point to one: in rank one this
is the projective-line degree normalization, and in rank d it is its ordered product.
An isomorphism pulls a rational point back to a rational point, with multiplicity one.
Consequently it preserves the top compact-support degree map, including the canonical
Tate coefficient comparison. Compact-support exchange identifies this fibre action with
the map displayed below. Both global compact-support sources have cohomology only in
degree zero. Exact inverse image and full faithfulness of the degree-zero embedding
reduce their trace equality to equality of module-sheaf maps, detected at all geometric
stalks. The comparison from pullback along the identity to the identity functor removes
the bottom identity edge; pullback composition supplies exactly the coefficient map.
At rank zero every fibre is a point and these are unit comparisons. The zero coefficient
ring and the empty base give the unique maps. No linearity or zero-section condition on
the isomorphism is used. This is only invariance over a fixed base, with no base-change
map between different bases and no exceptional inverse image.
-/
theorem vectorIntegration_presentationIso
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] [G.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π S d F)]
    [HasCompactification (VectorBundleZeroSection.π S d G)]
    [QuasiCompact (VectorBundleZeroSection.π S d G)]
    (e : VectorBundleZeroSection.scheme S d G ≅ VectorBundleZeroSection.scheme S d F)
    (he : e.hom ≫ VectorBundleZeroSection.π S d F = VectorBundleZeroSection.π S d G)
    (sq : IsPullback e.hom (VectorBundleZeroSection.π S d G)
      (VectorBundleZeroSection.π S d F) (𝟙 S)) :
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).inv.app
        (vectorIntegrationSource A N hA S d F) ≫
      (rightDerivedLowerShriekBaseChangeMap A sq).app
        (vectorIntegrationCoefficient A N hA S d F) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (VectorBundleZeroSection.π S d G)).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e.hom
          (VectorBundleZeroSection.π S d F) (VectorBundleZeroSection.π S d G)
          he.symm).inv.app (affineLinearBaseCoefficient A N hA S d)) ≫
      vectorBundleIntegration N hN A hA S hS d G =
    vectorBundleIntegration N hN A hA S hS d F := by sorry

end AlgebraicGeometry.Etale
