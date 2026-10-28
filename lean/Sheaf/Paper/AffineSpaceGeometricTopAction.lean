/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.AffineLinearTraceAction

/-! # The geometric top cohomology calculation for affine space -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- An automorphism over an algebraically closed field fixes the degree-zero homology
of the shifted, twisted compact-support object of affine space.

Source: latest blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2
(blueprint: lem-pur-affine-space-geometric-top-action).

Proof: use the ordered projective-line open-closed sequences to compute compactly
supported cohomology of affine d-space with the descended coefficient. It is concentrated
in degree zero after the twist and shift. The class of a rational point maps to one under
this ordered trace: in dimension one this is the Kummer normalization of a degree-one
point, and the product of these classes gives the statement in dimension d. These point
classes therefore generate. Pullback by the given isomorphism takes the class of a point
to that of its unique inverse image, with multiplicity one; functoriality of the Kummer
boundary gives exactly the coefficient comparison used in affineLinearTraceAction.
Consequently it fixes every generator. The rational geometric point of Spec(k) is
conservative on its small etale topos, so this module calculation gives equality of
the homology-sheaf maps. For d=0 this is the identity map on a point; for
the zero coefficient ring the homology sheaf is zero. No faithfulness of derived
pullback or descent from geometric points is asserted here.
-/
theorem affineSpaceIsoTraceAction_homology_zero
    (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (k : Type u) [Field k] [IsAlgClosed k]
    (hk : IsUnit (N : Γ(Spec (.of k), ⊤))) (d : ℕ)
    (e : affineTraceTower (Spec (.of k)) d ≅ affineTraceTower (Spec (.of k)) d)
    (sq : IsPullback e.hom (affineTraceProjection (Spec (.of k)) d)
      (affineTraceProjection (Spec (.of k)) d) (𝟙 (Spec (.of k)))) :
    (_root_.DerivedCategory.homologyFunctor
      (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} A)) 0).map
        (affineLinearTraceAction N hN A hA t (Spec (.of k)) hk d e.hom sq) = 𝟙 _ := by
  sorry

end AlgebraicGeometry.Etale
