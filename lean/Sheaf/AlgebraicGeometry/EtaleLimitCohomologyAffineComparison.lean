/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Sheaf.CategoryTheory.CohomologyColimitSites
import Sheaf.AlgebraicGeometry.FullAffineEtaleTopos
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.CategoryTheory.ColimitSites
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Affine-stage cohomology continuity

Source: Stacks Project, Tags 09YQ, 0EYL, 09YP and 04HR.
(blueprint: lem-weil-pbc-etale-limit-cohomology-affine-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Affine-stage continuity for the specified cohomology comparison.

Source: Stacks Project, Tags 09YQ (theorem-colimit), 0EYL
(lemma-colimit-affine-sites), 09YP (lemma-colimit), and 04HR.
(blueprint: lem-weil-pbc-etale-limit-cohomology-affine-comparison).

Proof:
1. Affine transition limits are affine. Present their affine etale sites as a
   filtered colimit using exists_affineEtaleSite_colimit, including its strictification.
2. Restriction along fullAffineEtaleInclusion is a sheaf equivalence. On an affine
   etale object A, both direct images evaluate a sheaf at the base change of A.
   This identifies the right adjoints under restriction. The induced isomorphism of
   left adjoints is the unique one compatible with the adjunction units. The two
   isomorphisms for a composite have the same unit, so uniqueness gives the
   composition compatibility. Transport phi by these isomorphisms; its two coherence
   equations therefore remain valid. Transport G and L using the same equivalences;
   an equivalence preserves the colimit and its legs.
3. Fix any index i and pass to the cofinal tail above i. The affine scheme D_i,
   with its identity map, is a final object of its affine etale site. Its base changes
   are the final objects D_j and X. Apply cohomology_colimit_of_sites to this object
   of the strictified site. Object cohomology at the final object is global
   cohomology. The sheaf equivalences identify these cohomology groups with the
   original groups, naturally in the coefficients.
4. The pullback comparisons agree: each is induced by the adjunction unit on
   injective resolutions, and step 2 identifies the units. Naturality in the
   coefficient sheaf identifies the transition maps with hH and the legs with hB.
   Thus the transported colimit cocone is exactly B, including eH and eB.
5. The tail inclusion is final, so its colimit is the colimit on I. Transport the
   colimit structure back to B. This yields Nonempty (IsColimit B).

Edge cases: nonemptiness gives the index chosen in the proof. Empty affine schemes
have zero cohomology. Degree zero uses sections. A one-object system identifies its
scheme limit and sheaf colimit with the single stage and its sheaf.
-/
theorem etale_limit_cohomology_affine_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, IsAffine (D.obj i)]
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L) (p : ℕ)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) p))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) p) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt p))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) p)) :
    Nonempty (IsColimit B) := by sorry

end AlgebraicGeometry.Etale
