/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Sheaf.CategoryTheory.RightDerivedSingleH0

/-!
# Degree-zero direct image and coefficient transition maps

Source: Stacks Project, derived.tex, Tag 05TD (`lemma-left-exact-higher-derived`),
and the normalized coefficient comparison
(blueprint: lem-pod-constant-tower-transition).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

private noncomputable abbrev restrictionDerivedUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
  F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K)

private theorem restrictionDerivedUnit_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] {K I : CochainComplex C ℤ} (j : K ⟶ I) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map j) ≫
        restrictionDerivedUnit F I =
      restrictionDerivedUnit F K ≫ F.rightDerivedFunctor.map (DerivedCategory.Q.map j) :=
  F.rightDerivedFunctorUnit.naturality ((HomotopyCategory.quotient _ _).map j)

private theorem h0_augmentation_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (H : D ⥤ C)
    (e : F ⋙ H ≅ 𝟭 C) {x y : C} {X Y : D}
    (u : F.obj x ⟶ X) (v : F.obj y ⟶ Y) (f : X ⟶ Y) (c : x ⟶ y)
    (i : H.obj X ≅ x) (j : H.obj Y ≅ y)
    (hu : H.map u ≫ i.hom = e.hom.app x)
    (hv : H.map v ≫ j.hom = e.hom.app y)
    (hc : u ≫ f = F.map c ≫ v) : i.inv ≫ H.map f ≫ j.hom = c := by
  apply (cancel_epi (e.hom.app x)).1
  conv_lhs => rw [← hu]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← H.map_comp_assoc, hc, H.map_comp, Category.assoc, hv]
  exact e.hom.naturality c

private theorem augmented_comparison_h0
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (T : A ⥤ C) (S : A ⥤ B) (U : C ⥤ D) (R : B ⥤ D) (H : D ⥤ C)
    (eta : T ⋙ U ⟶ S ⋙ R) (e : U ⋙ H ≅ 𝟭 C)
    {F G : A} (u : F ⟶ G) {y : C} (c : T.obj G ≅ y) {Y Z : D}
    (v : U.obj y ⟶ Y) (m : Y ≅ Z) (d : Z ≅ R.obj (S.obj G))
    (i : H.obj (R.obj (S.obj F)) ≅ T.obj F) (j : H.obj Y ≅ y)
    (hi : v ≫ m.hom ≫ d.hom = U.map c.inv ≫ eta.app G)
    (hu : H.map (eta.app F) ≫ i.hom = e.hom.app (T.obj F))
    (hv : H.map v ≫ j.hom = e.hom.app y)
    (a : T.obj F ⟶ H.obj (R.obj (S.obj F))) (b : T.obj G ⟶ H.obj Y)
    (ha : a = i.inv) (hb : c.hom ≫ j.inv = b)
    (q : R.obj (S.obj F) ⟶ Y)
    (hf : R.map (S.map u) ≫ d.inv ≫ m.inv = q) :
    a ≫ H.map q = T.map u ≫ b := by
  have hq : eta.app G ≫ d.inv ≫ m.inv = U.map c.hom ≫ v := by
    apply (cancel_mono m.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply (cancel_mono d.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hi, ← U.map_comp_assoc, Iso.hom_inv_id, U.map_id, Category.id_comp]
  have hn := eta.naturality u
  simp only [Functor.comp_map] at hn
  have hc : eta.app F ≫ (R.map (S.map u) ≫ d.inv ≫ m.inv) =
      U.map (T.map u ≫ c.hom) ≫ v := by
    rw [← Category.assoc, ← Category.assoc, ← hn]
    simp only [Category.assoc, hq, U.map_comp]
  have hz := h0_augmentation_square U H e (eta.app F) v
    (R.map (S.map u) ≫ d.inv ≫ m.inv) (T.map u ≫ c.hom) i j hu hv hc
  have hz' : i.inv ≫ H.map (R.map (S.map u) ≫ d.inv ≫ m.inv) =
      (T.map u ≫ c.hom) ≫ j.inv :=
    (Iso.eq_comp_inv j).2 (by simpa only [Category.assoc] using hz)
  rw [ha, ← hb, ← hf]
  simpa only [Category.assoc] using hz'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open AlgebraicGeometry.ProEtale in
private theorem single_unit_of_factors
    {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    [Abelian C] [Abelian D] [Abelian E] [Abelian V]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory V]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions E]
    (R : C ⥤ D) (T : E ⥤ V) (r : C ⥤ E) (s : D ⥤ V)
    [R.Additive] [T.Additive] [r.Additive] [s.Additive]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (t : R ⋙ s ⟶ r ⋙ T)
    (m : R.rightDerivedFunctor ⋙ s.mapDerivedCategory ⟶
      r.mapDerivedCategory ⋙ T.rightDerivedFunctor)
    (G : C)
    (h : s.mapDerivedCategory.map
          (restrictionDerivedUnit R ((CochainComplex.singleFunctor C 0).obj G)) ≫
        m.app ((DerivedCategory.singleFunctor C 0).obj G) ≫
        T.rightDerivedFunctor.map (r.mapDerivedCategoryFactors.hom.app
          ((CochainComplex.singleFunctor C 0).obj G)) =
      s.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor C 0).obj G)) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app
        ((CochainComplex.singleFunctor C 0).obj G)) ≫
      restrictionDerivedUnit T ((r.mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor C 0).obj G))) :
    R.mapSingleRightDerivedUnit s G ≫
      m.app ((DerivedCategory.singleFunctor C 0).obj G) ≫
      T.rightDerivedFunctor.map (r.exactSingleComparison.hom.app G) =
    (DerivedCategory.singleFunctor V 0).map (t.app G) ≫
      T.singleRightDerivedUnit.app (r.obj G) := by
  rw [Functor.mapSingleRightDerivedUnit_def, Functor.exactSingleComparison_def,
    Functor.exactSingleComparison_def]
  simp only [Category.assoc]
  let K := (CochainComplex.singleFunctor C 0).obj G
  let b := (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).inv.app G
  let c := (HomologicalComplex.singleMapHomologicalComplex r (.up ℤ) 0).hom.app G
  let d := (HomologicalComplex.singleMapHomologicalComplex s (.up ℤ) 0).inv.app (R.obj G)
  let a := (HomologicalComplex.singleMapHomologicalComplex T (.up ℤ) 0).inv.app (r.obj G)
  have hc : d ≫ (s.mapHomologicalComplex (.up ℤ)).map b ≫
      (NatTrans.mapHomologicalComplex t (.up ℤ)).app K =
      (CochainComplex.singleFunctor V 0).map (t.app G) ≫ a ≫
        (T.mapHomologicalComplex (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex r (.up ℤ) 0).inv.app G) := by
    apply HomologicalComplex.from_single_hom_ext
    dsimp only [a, b, d, K, CochainComplex.singleFunctor, CochainComplex.singleFunctors]
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Functor.map_comp,
      NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.single_map_f_self,
      Category.assoc, Iso.map_inv_hom_id_assoc]
    simp only [Functor.comp_obj, Iso.inv_hom_id_assoc]
    exact congrArg
      (fun z ↦ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (s.obj (R.obj G))).hom ≫ z)
      (t.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) 0 G).inv)
  have hs : (r.mapDerivedCategorySingleFunctor 0).hom.app G =
      r.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map c := by
    exact (Iso.inv_comp_eq (r.mapDerivedCategoryFactors.app K)).1
      (r.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app G)
  rw [Functor.singleRightDerivedUnit_app, Functor.singleRightDerivedUnit_app]
  change (s.mapDerivedCategorySingleFunctor 0).inv.app (R.obj G) ≫
    s.mapDerivedCategory.map (DerivedCategory.Q.map b ≫ restrictionDerivedUnit R K) ≫
      m.app (DerivedCategory.Q.obj K) ≫
      T.rightDerivedFunctor.map ((r.mapDerivedCategorySingleFunctor 0).hom.app G) = _
  rw [hs]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% h]
  erw [s.mapDerivedCategoryFactors.hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← Category.assoc]
  erw [s.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
  rw [← DerivedCategory.Q.map_comp_assoc, ← DerivedCategory.Q.map_comp_assoc]
  simp only [Category.assoc]
  change DerivedCategory.Q.map (d ≫ (s.mapHomologicalComplex (.up ℤ)).map b ≫
    (NatTrans.mapHomologicalComplex t (.up ℤ)).app K) ≫ _ = _
  rw [hc, DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp, Category.assoc,
    Category.assoc]
  erw [reassoc_of% (restrictionDerivedUnit_naturality T
    ((HomologicalComplex.singleMapHomologicalComplex r (.up ℤ) 0).inv.app G))]
  erw [← T.rightDerivedFunctor.map_comp, ← DerivedCategory.Q.map_comp]
  rw [Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

namespace AlgebraicGeometry.ProEtale

attribute [-instance] pbcRestriction_isRightAdjoint

attribute [local irreducible] upperStar

/-- The canonical augmentation isomorphism from ordinary direct image to degree-zero
unbounded derived direct image. The first comparison uses nonnegative injective
resolutions; the second is the inverse of the augmentation to the zeroth classical
right derived functor. Thus no arbitrary isomorphism is chosen.
Source: Stacks Project, Tag 05TD, part (3)
(blueprint: lem-pod-constant-tower-transition). -/
noncomputable def constantTowerTransitionAugmentation
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (lowerStar (ModuleCat.{u + 1} A) f).obj F ≅
      (DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) 0).obj
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor
            (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).obj F)) :=
  ((lowerStar (ModuleCat.{u + 1} A) f).singleRightDerivedH0Iso F).symm

/-- The derived coefficient comparison retains the ordinary direct-image section map
under the canonical degree-zero augmentations. The single/restriction comparison and
exact-restriction/homology comparison are included explicitly.
Source: Stacks Project, Tag 05TD, part (3), and the K-injective normalization of
lem-weil-proetale-direct-image-restriction-of-scalars
(blueprint: lem-pod-constant-tower-transition).

Proof: (1) On the small pro-etale sites take nonnegative injective resolutions
s : F[0] -> L, a : G[0] -> J, and b : (Res G)[0] -> I. Grothendieck existence
(prop-pur-kinjective-resolutions-exist, lem-sp-grothendieck-enough-injectives) supplies
these resolutions (lem-weil-pbc-left-exact-injective-resolution-degree-zero).
Their bounded-below injective terms make them K-injective
(lem-weil-pbc-bounded-below-injectives-kinjective). Restriction is exact.
(2) The Hom bijection into I (lem-weil-pbc-kinjective-hom-derived) lifts the two derived
maps to v : Res J -> I and h : L -> I. The equations v Res(a) = b and h s = b u[0]
hold strictly: a homotopy from a degree-zero complex into I has its only relevant
component in I^{-1} = 0. The first equation also makes v a quasi-isomorphism.
(3) Left exactness (lem-weil-proetale-module-direct-image-left-exact) gives the
augmentation isomorphisms alpha_F, alpha_G, alpha_r. The sectionwise formula
(def-weil-proetale-module-direct-image) identifies f_* Res with Res f_* on maps as
well as objects. Exactness identifies the restricted alpha_G with alpha'_G.
(4) Use lem-sf-kinjective-derived-map-computation for the map u. Apply
lem-sf-normalized-derived-comparison-common-resolution to a and v and the normalization
of lem-weil-proetale-direct-image-restriction-of-scalars: c is represented by
Q(f_*v) inverse. This does not assume that Res J is K-injective.
(5) Put V = H^0(f_*v), H = H^0(f_*h). Composing with degree-zero cycles inclusions
reduces V alpha'_G = alpha_r and H alpha_F = alpha_r f_*u to the strict chain equations
in (2). These inclusions are monic since all degree-minus-one terms vanish. Cancel V
to obtain V^{-1} H alpha_F = alpha'_G f_*u, the displayed equality. -/
theorem constantTowerTransition
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
    (u : F ⟶ (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj G) :
    (constantTowerTransitionAugmentation A f F).hom ≫
        (DerivedCategory.homologyFunctor
          (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) 0).map
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map
              ((DerivedCategory.singleFunctor
                (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).map u) ≫
            (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map
              (((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategorySingleFunctor
                0).inv.app G) ≫
            (fixedScalarRestrictionDirectImage φ f).hom.app
              ((DerivedCategory.singleFunctor
                (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) 0).obj G)) =
      (lowerStar (ModuleCat.{u + 1} A) f).map u ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).map
          (constantTowerTransitionAugmentation B f G).hom ≫
        ((Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategoryHomologyFunctorIso
          0).hom.app
          ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor.obj
            ((DerivedCategory.singleFunctor
              (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) 0).obj G)) := by
  let R := lowerStar (ModuleCat.{u + 1} B) f
  let T := lowerStar (ModuleCat.{u + 1} A) f
  let r := Sheaf.restrictScalars (Scheme.ProEt.topology X) φ
  let s := Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ
  rw [← Functor.exactSingleComparison_def r, ← Functor.exactH0Comparison_def s]
  let b : T.obj (r.obj G) ⟶ _ :=
    s.map (constantTowerTransitionAugmentation B f G).hom ≫
      s.exactH0Comparison.hom.app
        (R.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj G))
  exact augmented_comparison_h0 T (DerivedCategory.singleFunctor _ 0)
    (DerivedCategory.singleFunctor _ 0) T.rightDerivedFunctor
    (DerivedCategory.homologyFunctor _ 0) T.singleRightDerivedUnit
    (Functor.singleH0Comparison _) u
    ((fixedScalarRestrictionDirectImageUnderived φ f).symm.app G)
    (R.mapSingleRightDerivedUnit s G)
    ((fixedScalarRestrictionDirectImage φ f).symm.app
      ((DerivedCategory.singleFunctor _ 0).obj G))
    (T.rightDerivedFunctor.mapIso (r.exactSingleComparison.app G))
    (T.singleRightDerivedH0Iso F) (R.mapSingleRightDerivedH0Iso s G)
    (by simpa only [Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Iso.symm_inv,
        Iso.symm_hom, fixedScalarRestrictionDirectImage_inv, Category.assoc] using
      (single_unit_of_factors R T r s
        (fixedScalarRestrictionDirectImageUnderived φ f).hom
        (fixedScalarRestrictionDirectImageMap φ f) G
        (fixedScalarRestrictionDirectImageMap_factors φ f
          ((CochainComplex.singleFunctor _ 0).obj G))))
    (T.singleRightDerivedUnit_homology_zero F)
    (R.mapSingleRightDerivedUnit_homology_zero s G)
    (constantTowerTransitionAugmentation A f F).hom
    b
    (by rfl)
    (by
      dsimp only [b]
      simp only [Iso.app_hom, Iso.symm_hom, Functor.mapSingleRightDerivedH0Iso_inv]
      rw [fixedScalarRestrictionDirectImageUnderived_app_comp]
      rfl)
    (T.rightDerivedFunctor.map ((DerivedCategory.singleFunctor _ 0).map u) ≫
      T.rightDerivedFunctor.map (r.exactSingleComparison.inv.app G) ≫
      (fixedScalarRestrictionDirectImage φ f).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj G))
    (by simp only [Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv])

attribute [instance] pbcRestriction_isRightAdjoint

end AlgebraicGeometry.ProEtale
