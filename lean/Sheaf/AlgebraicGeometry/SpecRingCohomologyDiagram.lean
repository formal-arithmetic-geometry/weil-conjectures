/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # The canonical cohomology diagram of a ring system

Source: Stacks Project, Tags 09YQ.
(blueprint: lem-weil-pbc-spec-ring-cohomology-diagram)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Compatible maps from spectra of a ring diagram determine a cohomology diagram
and a cocone with the canonical pullback legs. No continuity assertion is made here.

Source: Stacks Project, Tag 09YQ, the cohomology diagram and comparison map.
(blueprint: lem-weil-pbc-spec-ring-cohomology-diagram)

Proof: Set H(a) to the cohomology of the inverse image of G along v(a).
For f : a to b, pull cohomology back along Spec(R(f)) and then apply the inverse
of the inverse-image composition isomorphism, using the given equation wv.
Naturality of pullback on cohomology and the composition coherence of inverse
image show that these maps compose. The identity coherence gives the identity
law. For the cocone vertex take the cohomology of the inverse image along vLimit.
Define the leg at a by pullback along Spec(c.ι(a)) followed by the inverse
composition isomorphism for wLimit(a). The cocone identity for c and the same
composition coherence prove naturality of these legs. Take eH and eB to be
identity isomorphisms. This construction does not use the colimit property of c,
filteredness, henselianness, or torsion; these are needed only by subsequent
continuity applications. It works for the zero ring and in degree zero. -/
theorem exists_spec_ring_cohomology_diagram
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (T : Scheme.{u}) (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (v : ∀ i : I, Spec (R.obj i) ⟶ T)
    (wv : ∀ (i j : I) (f : i ⟶ j), v j = Spec.map (R.map f) ≫ v i)
    (vLimit : Spec c.pt ⟶ T) (wLimit : ∀ i : I, vLimit = Spec.map (c.ι.app i) ≫ v i)
    (p : ℕ) :
    ∃ (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅
      AddCommGrpCat.of (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (v i)).obj G) p)),
    (∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom
        (cohomologyMap (Spec.map (R.map f))
          ((upperStar AddCommGrpCat.{u + 1} (v i)).obj G) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (Spec.map (R.map f)) (v i)
            (v j) (wv i j f)).inv.app G) p) ≫ (eH j).inv) ∧
    ∃ (B : Cocone H) (eB : B.pt ≅
      AddCommGrpCat.of (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} vLimit).obj G) p)),
    (∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom
        (cohomologyMap (Spec.map (c.ι.app i))
          ((upperStar AddCommGrpCat.{u + 1} (v i)).obj G) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (Spec.map (c.ι.app i)) (v i)
            vLimit (wLimit i)).inv.app G) p)) := by sorry

end AlgebraicGeometry.Etale
