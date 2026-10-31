/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.TensorMateInverseProjection
public import WeilConjectures.AlgebraicGeometry.EtaleSumExtensionTensor
public import WeilConjectures.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement

import all WeilConjectures.AlgebraicGeometry.EtaleSumRightAdjointTensor
import all WeilConjectures.AlgebraicGeometry.EtaleAmbientLeftComparisonBaseChange
import all WeilConjectures.AlgebraicGeometry.EtaleSupportMapCompatibility
import all WeilConjectures.AlgebraicGeometry.EtaleSumExtensionTensor
import all WeilConjectures.AlgebraicGeometry.ShriekTensorCompositionSupplement

/-! # The normalized projection square for etale precomposition

Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraph 3, expanded in step 3 of
lem-asd-tensor-mate-etale-precomp.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true

universe v

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance] derivedBraidedCategory _root_.DerivedCategory.braidedCategory'
attribute [local irreducible] Functor.mapDerivedCategory upperStar lowerStar
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  leftDerivedUpperStarIsoMapDerivedCategory etaleLowerShriek

private lemma canonical_sym_swap
    (C : Type*) [Category.{v + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{v + 1} C] [HasDerivedCategory.{v + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (K M : _root_.DerivedCategory C) :
    ((_root_.DerivedCategory.canonicalTensorSymmetry C).hom.app K).app M =
      ((_root_.DerivedCategory.canonicalTensorSymmetry C).inv.app M).app K := by
  let := _root_.DerivedCategory.symmetricCategory C
  exact SymmetricCategory.braiding_swap_eq_inv_braiding M K

private lemma canonical_sym_hom
    (C : Type*) [Category.{v + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{v + 1} C] [HasDerivedCategory.{v + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (K M : _root_.DerivedCategory C) :
    let := _root_.DerivedCategory.braidedCategory' C
    ((_root_.DerivedCategory.canonicalTensorSymmetry C).hom.app K).app M =
      (β_ K M).hom := by
  rfl

private lemma canonical_sym_inv
    (C : Type*) [Category.{v + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{v + 1} C] [HasDerivedCategory.{v + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C]
    [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (K M : _root_.DerivedCategory C) :
    let := _root_.DerivedCategory.braidedCategory' C
    ((_root_.DerivedCategory.canonicalTensorSymmetry C).inv.app K).app M =
      (β_ K M).inv := by
  rfl

private lemma sym_swap
    (A : Type (v + 1)) [CommRing A] (X : Scheme.{v})
    (K M : DerivedCategoryModule A X) :
    ((derivedTensorSymmetry (ModuleCat A) X).hom.app K).app M =
      ((derivedTensorSymmetry (ModuleCat A) X).inv.app M).app K := by
  exact canonical_sym_swap (Sheaf X.smallEtaleTopology (ModuleCat A)) K M

private lemma projection_iso
    (A : Type (v + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{v}} (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    IsIso (compactSupportProjectionMap A f M K) := by
  have := isIso_projectionMap_of_finite A f
  rw [compactSupportProjectionMap_eq]
  infer_instance

private lemma inv_inv_component
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D ⥤ E} (a : F ≅ G) (X : C) (Y : D) :
    inv ((a.inv.app X).app Y) = (a.hom.app X).app Y :=
  NatIso.inv_inv_app (a.app X) Y

private lemma inv_hom_component
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D ⥤ E} (a : F ≅ G) (X : C) (Y : D) :
    inv ((a.hom.app X).app Y) = (a.inv.app X).app Y :=
  NatIso.inv_hom_app (a.app X) Y

private lemma inverse_projection
    (A : Type (v + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{v}} (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    let _ := projection_iso A f M K
    inv (compactSupportProjectionMap A f M K) =
      (tensorMateInverseProjection A f K).app M := by
  have := projection_iso A f M K
  have := isIso_projectionMap_of_finite A f
  dsimp only
  simp only [compactSupportProjectionMap_eq]
  simp only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app,
    inv_inv_component, inv_hom_component, tensorMateInverseProjection,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    evaluation_obj_map, flipFunctor_map_app_app, NatIso.isIso_inv_app,
    Functor.comp_obj, Category.assoc]
  let F := rightDerivedLowerShriek (ModuleCat A) f
  let l := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) f
  have hn := NatTrans.congr_app
    ((derivedTensorSymmetry (ModuleCat A) X).hom.naturality (l.inv.app K)) M
  simp only [NatTrans.comp_app, Functor.flip_map_app] at hn
  rw [sym_swap A Y (F.obj M) K]
  rw [← F.map_comp_assoc, ← F.map_comp_assoc, hn]

private lemma sum_swap
    (A : Type (v + 1)) [CommRing A]
    {V T : Scheme.{v}} (e : V ⟶ T)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (M : DerivedCategoryModule A V) (K : DerivedCategoryModule A T) :
    ((etaleSupportSumProjectionReverse A e).app M).app K =
      (etaleLowerShriek (ModuleCat A) e inferInstance).mapDerivedCategory.map
        (((derivedTensorSymmetry (ModuleCat A) V).hom.app M).app
          ((upperStar (ModuleCat A) e).mapDerivedCategory.obj K)) ≫
      etaleSumExtensionTensorComparison A e K M ≫
        ((derivedTensorSymmetry (ModuleCat A) T).inv.app
          ((etaleLowerShriek (ModuleCat A) e inferInstance).mapDerivedCategory.obj M)).app K := by
  let := leftDerivedUpperStarMonoidal (ModuleCat A) e
  let l := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) e
  let := Functor.Monoidal.transport l
  let adj := (etaleLowerShriekUpperStarAdjunction (ModuleCat A) e
    inferInstance).mapDerivedCategoryAdjunction
  have hμ := exactUpperStar_mu_eq (ModuleCat A) e
  have hb := braided_transport l
    (leftDerivedUpperStar_μ_map_braiding_hom (ModuleCat A) e)
  have hQ : etaleSumExtensionTensorComparison A e K M =
      (Functor.Monoidal.projectionMap adj K).app M := by
    simp only [etaleSumExtensionTensorComparison, Adjunction.homEquiv_counit,
      Functor.Monoidal.projectionMap, Functor.map_comp, Category.assoc]
    rw [show (etaleSumExtensionTensorPullbackIso A e K _).hom =
      Functor.LaxMonoidal.μ (upperStar (ModuleCat A) e).mapDerivedCategory K _ from
        (hμ K _).symm]
    rfl
  rw [hQ]
  have h := rightProjection_eq_braiding adj hb M K
  change (etaleLowerShriek (ModuleCat A) e inferInstance).mapDerivedCategory.map
      ((adj.unit.app M) ▷ (upperStar (ModuleCat A) e).mapDerivedCategory.obj K ≫
        (etaleSumExtensionTensorPullbackIso A e
          ((etaleLowerShriek (ModuleCat A) e inferInstance).mapDerivedCategory.obj M) K).hom) ≫
      adj.counit.app _ = _
  rw [show (etaleSumExtensionTensorPullbackIso A e _ K).hom =
      Functor.LaxMonoidal.μ (upperStar (ModuleCat A) e).mapDerivedCategory _ K from
        (hμ _ K).symm]
  simpa only [derivedTensor, curriedTensor_obj_obj, derivedTensorSymmetry,
    canonical_sym_hom, canonical_sym_inv] using h

private theorem projection_glue
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F L : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    (TD : D ⥤ D) (TE : E ⥤ E) (a : F ≅ L) (e : F ⋙ G ≅ H)
    (s : TD ⋙ G ⟶ G ⋙ TE) (M P : C)
    (q : L.obj P ⟶ TD.obj (L.obj M))
    (r : F.obj P ⟶ TD.obj (F.obj M))
    (h : H.obj P ⟶ TE.obj (H.obj M))
    (hq : a.hom.app P ≫ q = r ≫ TD.map (a.hom.app M))
    (ht : G.map r ≫ s.app (F.obj M) ≫ TE.map (e.hom.app M) =
      e.hom.app P ≫ h) :
    let c := Functor.isoWhiskerRight a.symm G ≪≫ e
    G.map q ≫ s.app (L.obj M) ≫ TE.map (c.hom.app M) = c.hom.app P ≫ h := by
  have hqi : q ≫ TD.map (a.inv.app M) = a.inv.app P ≫ r := by
    apply (cancel_epi (a.hom.app P)).1
    rw [← Category.assoc, hq]
    simp only [Category.assoc, ← TD.map_comp, Iso.hom_inv_id_app,
      TD.map_id, Category.comp_id, Iso.hom_inv_id_app_assoc]
  dsimp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerRight_app]
  rw [TE.map_comp]
  have hn := s.naturality (a.inv.app M)
  simp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← reassoc_of% hn, ← G.map_comp_assoc, hqi, G.map_comp]
  simp only [Category.assoc]
  rw [ht]

private lemma conjugate_projection
    {C D : Type*} [Category C] [Category D]
    {F E : C ⥤ D} (a : F ≅ E) (W : D ⥤ D ⥤ D) (s : W ≅ W.flip)
    (M P Q : C) (K : D)
    (p : (W.obj (F.obj M)).obj K ⟶ F.obj P) (b : P ⟶ Q)
    (q : E.obj Q ⟶ (W.obj K).obj (E.obj M))
    (hp : p ≫ a.hom.app P ≫ E.map b ≫ q ≫ (s.hom.app K).app (E.obj M) =
      (W.map (a.hom.app M)).app K) :
    (s.hom.app K).app (F.obj M) ≫ p ≫ F.map b ≫ a.hom.app Q ≫ q =
      (W.obj K).map (a.hom.app M) := by
  apply (cancel_mono ((s.hom.app K).app (E.obj M))).1
  simp only [Category.assoc]
  rw [reassoc_of% (a.hom.naturality b), hp]
  exact ((s.hom.app K).naturality (a.hom.app M)).symm

private lemma conjugate_inverse
    {C : Type*} [Category C] {X Y Z W : C}
    (e : X ≅ Y) (d : Z ≅ W) (r : X ⟶ Z) (h : Y ⟶ W)
    (hi : e.inv ≫ r = h ≫ d.inv) : r ≫ d.hom = e.hom ≫ h := by
  apply (cancel_epi e.inv).1
  rw [← Category.assoc, hi]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc]

private lemma normalization_projection_forward
    (A : Type (v + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {V T : Scheme.{v}} (e : V ⟶ T)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [IsNoetherian V] [IsNoetherian T]
    (c : Compactification e) (M : DerivedCategoryModule A V) (K : DerivedCategoryModule A T) :
    let a := N.comparison e c
    compactSupportProjectionMapOfCompactification A c M K ≫
        a.hom.app (((derivedTensor (ModuleCat A) V).obj
          ((upperStar (ModuleCat A) e).mapDerivedCategory.obj K)).obj M) ≫
        etaleSumExtensionTensorComparison A e K M =
      ((derivedTensor (ModuleCat A) T).obj K).map (a.hom.app M) := by
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat A) c
  let E := (etaleLowerShriek (ModuleCat A) e inferInstance).mapDerivedCategory
  let D := (upperStar (ModuleCat A) e).mapDerivedCategory
  let U := derivedTensor (ModuleCat A) V
  let W := derivedTensor (ModuleCat A) T
  let a := N.comparison e c
  let b := ((derivedTensorSymmetry (ModuleCat A) V).inv.app (D.obj K)).app M
  have hp := tensorProjectionCompatibility A N e c M K
  rw [sum_swap, sym_swap A V M (D.obj K)] at hp
  rw [← sym_swap A T K (E.obj M)] at hp
  have hc := conjugate_projection a W (derivedTensorSymmetry (ModuleCat A) T)
    M ((U.obj M).obj (D.obj K)) ((U.obj (D.obj K)).obj M) K
    (((projectionMapOfCompactification (ModuleCat A) c).app M).app K ≫
      F.map ((U.obj M).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) e).hom.app K)))
    b (etaleSumExtensionTensorComparison A e K M) (by
      simpa only [F, U, D, W, a, b, E, Category.assoc] using hp)
  simpa only [compactSupportProjectionMapOfCompactification,
    F, U, D, W, a, b, E, Category.assoc] using hc

private lemma normalization_projection
    (A : Type (v + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {V T : Scheme.{v}} (e : V ⟶ T)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [IsNoetherian V] [IsNoetherian T] [HasCompactification e]
    (M : DerivedCategoryModule A V) (K : DerivedCategoryModule A T) :
    let a := N.comparison e (HasCompactification.compactification e)
    a.hom.app (((derivedTensor (ModuleCat A) V).obj
          ((upperStar (ModuleCat A) e).mapDerivedCategory.obj K)).obj M) ≫
        etaleSumExtensionTensorComparison A e K M =
      (tensorMateInverseProjection A e K).app M ≫
        ((derivedTensor (ModuleCat A) T).obj K).map (a.hom.app M) := by
  have := projection_iso A e M K
  rw [← inverse_projection]
  apply (cancel_epi (compactSupportProjectionMap A e M K)).1
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  simpa only [Category.assoc, compactSupportProjectionMap] using
    normalization_projection_forward A N e (HasCompactification.compactification e) M K

/-- The coefficient-first inverse projections intertwine the graph-normalized etale
compact-support compositor and the sum-extension projection.
Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraph 3; Stacks Tag 0GL5;
step 3 of lem-asd-tensor-mate-etale-precomp
(blueprint: lem-asd-etale-precomp-projection).

Proof: Fix the chosen compactifications of f and h = u ≫ f. Their proper/open tower
uses the induced compactification of u. Apply compactSupportProjectionMap_comp and
compactSupportProjectionMap_comparison to identify its projection with the projection
for h. The graph-normalized comparison of etaleSupportMapCompatibility identifies
the compact-support projection for u with the sum-extension projection: both inverse
comparisons extend a sheet section by zero from its graph. Uniqueness follows by
embedding the sheaf comparison into direct image and then descending its prescribed
map on homotopy representatives. Thus this comparison equals N.comparison at the
induced compactification. Transport the tower equation along that comparison.
Conjugate by the signed tensor symmetries and the exact-pullback comparisons, then
invert the three projection maps. Naturality moves the compositor past these changes
of presentation; the pullback-composition comparison supplies the displayed map on
the first tensor factor. The result is precisely the equation below, for arbitrary
unbounded K and M. The argument uses no exceptional right adjoint or dualizing object.
-/
theorem etalePrecompProjection
    (A : Type (v + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X S : Scheme.{v}} (u : U ⟶ X) (f : X ⟶ S)
    [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated (u ≫ f)] [LocallyOfFiniteType (u ≫ f)] [QuasiCompact (u ≫ f)]
    [HasCompactification f] [HasCompactification (u ≫ f)]
    (K : DerivedCategoryModule A S) (M : DerivedCategoryModule A U) :
    let c := etaleAmbientLeftComparison A N u f
      (HasCompactification.compactification f)
      (HasCompactification.compactification (u ≫ f))
    R(f)_![ModuleCat A].map
        (etaleSumExtensionTensorComparison A u
          ((f)^*[ModuleCat A].mapDerivedCategory.obj K) M) ≫
        (tensorMateInverseProjection A f K).app
          ((etaleLowerShriek (ModuleCat A) u inferInstance).mapDerivedCategory.obj M) ≫
        ((derivedTensor (ModuleCat A) S).obj K).map (c.hom.app M) =
      c.hom.app (((derivedTensor (ModuleCat A) U).obj
          ((u)^*[ModuleCat A].mapDerivedCategory.obj
            ((f)^*[ModuleCat A].mapDerivedCategory.obj K))).obj M) ≫
        R(u ≫ f)_![ModuleCat A].map
          (((derivedTensor (ModuleCat A) U).map
            ((unboundedEtaleUpperStarCompIso A u f).inv.app K)).app M) ≫
        (tensorMateInverseProjection A (u ≫ f) K).app M := by
  let B := (upperStar (ModuleCat A) f).mapDerivedCategory.obj K
  let E := (etaleLowerShriek (ModuleCat A) u inferInstance).mapDerivedCategory
  let F := rightDerivedLowerShriek (ModuleCat A) u
  let G := rightDerivedLowerShriek (ModuleCat A) f
  let H := rightDerivedLowerShriek (ModuleCat A) (u ≫ f)
  let P := ((derivedTensor (ModuleCat A) U).obj
    ((upperStar (ModuleCat A) u).mapDerivedCategory.obj B)).obj M
  let T := (derivedTensor (ModuleCat A) X).obj B
  let W := (derivedTensor (ModuleCat A) S).obj K
  let a := N.comparison u (HasCompactification.compactification u)
  let e := unboundedEtaleLowerShriekCompIso A u f
  have := projection_iso A u M B
  have := projection_iso A f (F.obj M) K
  have := projection_iso A (u ≫ f) M K
  have hi := (compactSupportProjectionMap_comp A u f M K).2
  simp only [inverse_projection] at hi
  have ht : G.map ((tensorMateInverseProjection A u B).app M) ≫
      (tensorMateInverseProjection A f K).app (F.obj M) ≫ W.map (e.hom.app M) =
      e.hom.app P ≫ H.map
        (((derivedTensor (ModuleCat A) U).map
          ((unboundedEtaleUpperStarCompIso A u f).inv.app K)).app M) ≫
        (tensorMateInverseProjection A (u ≫ f) K).app M := by
    simpa only [Category.assoc, Functor.mapIso_hom, Iso.app_hom] using
      conjugate_inverse (e.app P) (W.mapIso (e.app M))
      (G.map ((tensorMateInverseProjection A u B).app M) ≫
        (tensorMateInverseProjection A f K).app (F.obj M))
      (H.map (((derivedTensor (ModuleCat A) U).map
          ((unboundedEtaleUpperStarCompIso A u f).inv.app K)).app M) ≫
        (tensorMateInverseProjection A (u ≫ f) K).app M)
      (by simpa only [Functor.mapIso_inv, Iso.app_inv, e, W, P, B, F, G, H,
        Category.assoc] using hi)
  rw [left_comparison_chosen]
  exact projection_glue T W a e (tensorMateInverseProjection A f K) M P
    (etaleSumExtensionTensorComparison A u B M)
    ((tensorMateInverseProjection A u B).app M)
    (H.map (((derivedTensor (ModuleCat A) U).map
        ((unboundedEtaleUpperStarCompIso A u f).inv.app K)).app M) ≫
      (tensorMateInverseProjection A (u ≫ f) K).app M)
    (normalization_projection A N u M B) ht

end AlgebraicGeometry.Etale
