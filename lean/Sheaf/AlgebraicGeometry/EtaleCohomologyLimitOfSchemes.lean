/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Etale cohomology of limits of schemes

Source: Stacks Project, Etale Cohomology, Theorem 59.51.3 (Tag 09YQ), and
Limits, Lemma 32.2.1 (Tag 01YW)
(blueprint: lem-weil-pbc-etale-cohomology-limit-of-schemes).

The object isomorphisms present diagrams on the varying sites as ordinary functors.
The equations on their arrows and on the cocone legs specify the canonical comparison.
Its being a colimit cocone says that the induced comparison from the colimit is an
isomorphism. We use `Sheaf.H` and `cohomologyMap`, the recorded abelian-sheaf cohomology
and pullback encoding; its comparison with K-injective cohomology is a stage-3 bridge.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Cohomology continuity for a system of abelian sheaves on a directed inverse system
of qcqs schemes with affine transition maps. Source: Stacks Project, Tag 09YQ
(blueprint: lem-weil-pbc-etale-cohomology-limit-of-schemes).

Proof:
1. Inverse-image composition (lem-weil-pbc-inverse-image-composition) and its coherence
   turn the pulled-back sheaves into the diagram `G`. Cohomology pullback functoriality
   (lem-weil-pbc-cohomology-pullback-functorial) gives the diagram `H` and cocone `B`.
2. Restrict to any cofinal tail of the directed set using
   lem-weil-pbc-colimit-initial-full-subcategory and lem-weil-pbc-limit-affine-transition.
3. For affine stages use lem-weil-pbc-affine-etale-site-topos and
   lem-weil-pbc-affine-etale-site-colimit to pass to the colimit of affine etale sites.
   Direct images agree on affine objects, so uniqueness of left adjoints identifies
   inverse images, compatibly with units and composition.
4. Apply lem-weil-pbc-cohomology-colimit-of-sites at the final affine object and transport
   the cohomology comparison back across the equivalence. Cofinality gives the full diagram.
5. Restrict to quasi-compact opens at a stage. Limits commute with these restrictions,
   and inverse image preserves colimits; hence the restricted data have the same form.
6. Mayer-Vietoris and its pullback compatibility (lem-weil-pbc-etale-mayer-vietoris and
   lem-weil-pbc-etale-mayer-vietoris-pullback), exact filtered colimits of abelian groups
   (lem-weil-pbc-filtered-colimit-abelian-groups-exact), and lem-weil-pbc-five-lemma
   show that the result glues across two such opens.
7. Induct on a finite affine cover in the separated case; intersections of affine opens
   are affine by lem-weil-pbc-separated-affine-open-intersection.
8. Induct on a finite affine cover in general. The intersection with one affine is a
   quasi-compact separated open, handled by step 7. Step 6 finishes the induction.
   The comparison throughout has exactly the legs prescribed by `hB`.
-/
theorem nonempty_isColimit_etale_cohomology_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
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
    Nonempty (IsColimit B) := by
  sorry

/-- The affine ring case: for a directed system of rings with colimit `C`, the compatible
pullbacks of one abelian sheaf to `Spec C_i` satisfy continuity at `Spec C`.
Source: Stacks Project, Tags 01YW and 09YQ
(blueprint: lem-weil-pbc-etale-cohomology-limit-of-schemes).

Proof (step 9 of the node): lem-weil-pbc-spec-colimit-limit gives the limit and affine
transitions. Set F_i = v_i inverse image of G; inverse-image composition gives their
transition isomorphisms and the cocycle law. On the limit all these sheaves identify with
v inverse image of G, with identity transition maps. The directed index is connected,
so lem-weil-pbc-colimit-constant-connected-diagram identifies their colimit with that
sheaf. Apply the preceding eight-step argument. Its canonical maps become the pullbacks
followed by the composition isomorphisms appearing in `hH` and `hB` below. -/
theorem nonempty_isColimit_etale_cohomology_spec_ring_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (T : Scheme.{u}) (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (v : ∀ i : I, Spec (R.obj i) ⟶ T)
    (wv : ∀ (i j : I) (f : i ⟶ j), v j = Spec.map (R.map f) ≫ v i)
    (vLimit : Spec c.pt ⟶ T) (wLimit : ∀ i : I, vLimit = Spec.map (c.ι.app i) ≫ v i)
    (p : ℕ) (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅
      AddCommGrpCat.of (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (v i)).obj G) p))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom
        (cohomologyMap (Spec.map (R.map f))
          ((upperStar AddCommGrpCat.{u + 1} (v i)).obj G) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (Spec.map (R.map f)) (v i)
            (v j) (wv i j f)).inv.app G) p) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅
      AddCommGrpCat.of (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} vLimit).obj G) p))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom
        (cohomologyMap (Spec.map (c.ι.app i))
          ((upperStar AddCommGrpCat.{u + 1} (v i)).obj G) p) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map
          ((upperStarComp AddCommGrpCat.{u + 1} (Spec.map (c.ι.app i)) (v i)
            vLimit (wLimit i)).inv.app G) p)) :
    Nonempty (IsColimit B) := by
  sorry

end AlgebraicGeometry.Etale
