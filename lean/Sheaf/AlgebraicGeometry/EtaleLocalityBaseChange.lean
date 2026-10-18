/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction
import Sheaf.AlgebraicGeometry.EtaleSetBaseChangeLocalTransport
import Sheaf.AlgebraicGeometry.EtaleDerivedBaseChangeLocalTransport
import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Etale locality of base change

Source: Stacks Project, Tag 0EZR, Lemma `lemma-base-change-local`; blueprint,
sec-smooth-base-change, sk-def-bc (blueprint: sbc-lem-etale-locality).
-/

@[expose] public section

universe u w

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isIso_of_localizationRestriction
    (A : Type*) [Category.{u + 1} A]
    {X : Scheme.{u}} {ι : Type w} {U : ι → Scheme.{u}}
    (a : ∀ i, U i ⟶ X) [∀ i, AlgebraicGeometry.Etale (a i)]
    (ha : ∀ x : X, ∃ (i : ι) (y : U i), (a i).base y = x)
    {F G : Sheaf X.smallEtaleTopology A} (φ : F ⟶ G)
    (hφ : ∀ i, IsIso ((localizationRestriction A (a i) inferInstance).map φ)) :
    IsIso φ := by
  let V : ι → X.Etale := fun i => Scheme.Etale.mk (a i)
  have hV : X.smallEtaleTopology.CoversTop V := by
    rw [X.smallEtaleTopology.coversTop_iff_of_isTerminal (Scheme.Etale.mk (𝟙 X))
      (Scheme.Etale.isTerminalMkId X)]
    rw [Scheme.mem_smallEtaleTopology_iff]
    intro x
    obtain ⟨i, y, hy⟩ := ha x
    refine ⟨V i, MorphismProperty.Over.homMk (a i) ?_, ?_, y, hy⟩
    · change a i ≫ 𝟙 X = a i
      exact Category.comp_id _
    · exact ⟨i, ⟨𝟙 _⟩⟩
  apply Sheaf.isIso_of_coversTop hV
  intro i
  have := hφ i
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  rintro ⟨Z⟩
  let W : (U i).Etale := Scheme.Etale.mk Z.hom.left
  have hW : IsIso
      (((localizationRestriction A (a i) inferInstance).map φ).hom.app (Opposite.op W)) :=
    inferInstance
  let e : ((MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale (a i))).obj W)
      ≅ Z.left :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ Z.left.hom = Z.hom.left ≫ a i
      rw [Category.id_comp]
      exact (show Z.hom.left ≫ a i = Z.left.hom from
        MorphismProperty.Over.w Z.hom).symm)
  exact (NatTrans.isIso_app_iff_of_iso φ.hom e.op).2 hW


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem isIso_of_upperStar
    {X : Scheme.{u}} {ι : Type w} {U : ι → Scheme.{u}}
    (a : ∀ i, U i ⟶ X) [∀ i, AlgebraicGeometry.Etale (a i)]
    (ha : ∀ x : X, ∃ (i : ι) (y : U i), (a i).base y = x)
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (hφ : ∀ i, IsIso ((upperStar AddCommGrpCat.{u + 1} (a i)).map φ)) :
    IsIso φ := by
  apply isIso_of_localizationRestriction AddCommGrpCat.{u + 1} a ha
  intro i
  exact (NatIso.isIso_map_iff
    (upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} (a i) inferInstance) φ).1
    (hφ i)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Etale locality for sets, unbounded abelian complexes, and a single cohomological degree.
The chosen local squares are the associated Cartesian squares: `hc` identifies `T' i`
with `V i ×[S] T`, and `wfactor` and `localSquare` identify `Y' i` with `U i ×[X] Y`.
The displayed equalities in Stacks mean invertibility of the canonical exchange arrows.
Source: Stacks Project, Tag 0EZR (blueprint: sbc-lem-etale-locality).

Proof:
1. Etale base change makes `c i` and the induced `Y' i → Y` etale
   (lem-weil-pbc-etale-base-change-finite-limits). The equivalence of an etale object's
   site with the slice site (lem-weil-pbc-etale-site-localization-open) respects coverings
   and the sheaf equalizer condition. Under this equivalence, localized inverse image is
   restriction (def-pur-localized-ringed-site). For an etale morphism `j : B → W`,
   composition from the site of B to that of W is left adjoint to base change: a map to
   `B ×[W] Q` over B is precisely a map to Q over W. Both functors preserve sheaves,
   using lem-weil-pbc-etale-base-change-continuous. By
   lem-weil-pbc-sets-adjoint-continuous-restriction-adjunction, restriction is therefore
   `j⁻¹`, with unit given by restriction along `Q ×[W] B → Q`; the same holds for
   abelian sheaves. Apply lem-weil-pbc-slice-site-localization to g at V_i and h at U_i.
   It identifies restricted pushforwards with local pushforwards. Apply the inverse-image
   composition comparison (lem-weil-pbc-site-morphism-composition) to the two commuting
   triangles. This identifies both restricted sides with the sides of the local map.
2. For an arbitrary unbounded complex choose a K-injective representative I by
   prop-pur-kinjective-resolutions-exist. Its restrictions remain K-injective by
   lem-pur-kinjective-restrict-localized. Direct image is sectionwise additive, so preserves
   finite biproducts, shifts, and the matrices defining cones. Thus it is triangulated on
   homotopy categories and lem-weil-pbc-kinjective-total-derived computes the direct images
   by g_* I and the local g_i* of its restriction. The termwise comparison of step 1 gives
   the derived pushforward comparison. Restriction and inverse image are exact
   (lem-weil-pbc-site-restriction-exact, prop-weil-pbc-inverse-image-exact); by
   lem-weil-pbc-exact-functor-derived-factorization their derived functors act termwise.
   Applying the inverse-image comparisons termwise identifies both derived sides.
3. These comparisons identify the arrows, not just their source and target objects.
   For sets the transpose under h⁻¹ ⊣ h_* is the inverse-image square comparison followed
   by e⁻¹ of the counit for g. The direct-image localization comparison is the identity on
   sections over the canonically identified fibre products. Its adjoint carries the counit
   to the local counit, since both correspond to the identity under the same adjunction.
   Transposing therefore identifies the restricted exchange with the local exchange.
   For complexes, choose I representing K and a K-injective resolution e⁻¹ I → J.
   Pushforward preserves K-injectives: adjunction identifies maps and homotopies from an
   acyclic N to v_* P with those from v⁻¹ N to P, and exactness makes v⁻¹ N acyclic.
   By lem-weil-pbc-kinjective-hom-derived the derived counit is consequently represented
   by the termwise counit. The global arrow is represented by f⁻¹ g_* I → h_* J,
   adjoint to the square comparison, e⁻¹ of the counit, and the resolution map.
   This is the unit-composition-counit formula of sbc-def-base-change-map: transpose it
   twice, use naturality to move the unit through the composition comparison, then cancel
   adjacent unit and counit by the triangle identity. Restrict I and J; their restrictions
   remain K-injective and the restricted resolution remains a quasi-isomorphism by exactness.
   Thus the restricted chain map represents precisely the local exchange map. No claim
   that arbitrary inverse image preserves K-injectives is used.
4. For sets, on any etale W over X, the pullbacks of the U_i cover W. Unique local inverse
   images of a section agree on overlaps because the local maps are injective. The sheaf
   equalizer glues them uniquely, proving bijectivity on sections; uniqueness makes the
   inverse natural. This includes the empty cover of the empty scheme.
5. For unbounded complexes restriction commutes with every H^r by exactness. Steps 2 and 3
   show H^r of the global map is locally invertible. Use
   lem-weil-pbc-etale-cover-detects-iso for every integer r, then
   lem-weil-pbc-unbounded-derived-iso-cohomology. There is no lower or uniform bound.
6. Put an abelian sheaf in degree zero. By sbc-def-base-change-map, the degree-q map is
   H^q of its exchange. Exact restriction commutes with kernels, images and quotients, so
   steps 2 and 3 identify its restriction with the local degree-q map. Apply
   lem-weil-pbc-etale-cover-detects-iso in this degree alone, without any hypothesis on the
   other degrees. This works for every integer q. -/
theorem etale_locality_baseChange
    {X Y S T : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g)
    {ι : Type w} {U V T' Y' : ι → Scheme.{u}}
    (a : ∀ i, U i ⟶ X) [∀ i, AlgebraicGeometry.Etale (a i)]
    (ha : ∀ x : X, ∃ (i : ι) (y : U i), (a i).base y = x)
    (fi : ∀ i, U i ⟶ V i) (b : ∀ i, V i ⟶ S)
    [∀ i, AlgebraicGeometry.Etale (b i)]
    (wfactor : ∀ i, fi i ≫ b i = a i ≫ f)
    (c : ∀ i, T' i ⟶ T) (gi : ∀ i, T' i ⟶ V i)
    (hc : ∀ i, IsPullback (c i) (gi i) g (b i))
    (ei : ∀ i, Y' i ⟶ T' i) (hi : ∀ i, Y' i ⟶ U i)
    (localSquare : ∀ i, ChosenCartesianSquare (hi i) (ei i) (fi i) (gi i)) :
    (∀ F : Sheaf T.smallEtaleTopology (Type (u + 1)),
      (∀ i, IsIso (setBaseChangeArrow (localSquare i)
        ((Scheme.etaleSetPullback (c i)).obj F))) →
      IsIso (setBaseChangeArrow sq F)) ∧
    (∀ K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ i, IsIso (abelianDerivedBaseChangeArrow (localSquare i)
        (D(upperStar AddCommGrpCat.{u + 1} (c i)).obj K))) →
      IsIso (abelianDerivedBaseChangeArrow sq K)) ∧
    (∀ (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ),
      (∀ i, IsIso ((DerivedCategory.homologyFunctor _ q).map
        (abelianDerivedBaseChangeArrow (localSquare i)
          ((DerivedCategory.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{u + 1} (c i)).obj F))))) →
      IsIso ((DerivedCategory.homologyFunctor _ q).map
        (abelianDerivedBaseChangeArrow sq ((DerivedCategory.singleFunctor _ 0).obj F)))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro F hF
    apply isIso_of_localizationRestriction (Type (u + 1)) a ha
    intro i
    obtain ⟨ρ, _⟩ := etaleSetInverseImageRestriction (a i)
    exact (NatIso.isIso_map_iff ρ (setBaseChangeArrow sq F)).1
      (setBaseChangeArrow_local_isIso sq (a i) (fi i) (b i) (wfactor i)
        (c i) (gi i) (hc i) (localSquare i) F (hF i))
  · intro K hK
    apply (DerivedCategory.isIso_iff _ _).2
    intro q
    apply isIso_of_upperStar a ha
    intro i
    have := hK i
    exact abelianDerivedBaseChangeArrow_local_homology_isIso sq (a i) (fi i) (b i)
      (wfactor i) (c i) (gi i) (hc i) (localSquare i) K q (by infer_instance)
  · intro F q hF
    apply isIso_of_upperStar a ha
    intro i
    apply abelianDerivedBaseChangeArrow_local_homology_isIso sq (a i) (fi i) (b i)
      (wfactor i) (c i) (gi i) (hc i) (localSquare i)
      ((DerivedCategory.singleFunctor _ 0).obj F) q
    exact (NatTrans.isIso_app_iff_of_iso
      (Functor.whiskerRight (abelianDerivedBaseChangeTransformation (localSquare i))
        (DerivedCategory.homologyFunctor _ q))
      (((upperStar AddCommGrpCat.{u + 1} (c i)).mapDerivedCategorySingleFunctor 0).app F)).2
      (hF i)

end AlgebraicGeometry.Etale
