/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.SectionDerivedRealization
public import Sheaf.CategoryTheory.ExactDerivedAdjunction
public import Sheaf.Paper.SectionOpenGeneratorScalar
import Sheaf.CategoryTheory.DerivedCategory.AdjunctionMateTranspose

/-! # Section equivalence and the canonical derived open adjunction

Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ; Derived Categories,
Tag 015F (blueprint: lem-pd-section-derived-open-adjunction-normalization).

The extension comparison and pullback comparison are the fixed comparisons already
in the library. The two adjunctions below independently localize the ordinary
adjunctions; neither is defined by transport through the section equivalences.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

private theorem normalizedMate_hom
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {Lb : C ⥤ D} {Rb : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a : L ⊣ R) (b : Lb ⊣ Rb)
    (e : L ⋙ H ≅ G ⋙ Lb) (r : R ⋙ G ≅ H ⋙ Rb)
    (hm : (mateEquiv a b e.inv).natTrans = r.hom)
    (M : A) (N : B) (q : L.obj M ⟶ N) :
    b.homEquiv _ _ (e.inv.app M ≫ H.map q) = G.map (a.homEquiv _ _ q) ≫ r.hom.app N := by
  have he : ((mateEquiv a b).symm r.hom).natTrans = e.inv := by
    rw [← hm]
    exact congrArg TwoSquare.natTrans ((mateEquiv a b).symm_apply_apply e.inv)
  have h := adjunctionMate_transpose a b r.hom M N q
  change b.homEquiv _ _ (((mateEquiv a b).symm r.hom).natTrans.app M ≫ H.map q) = _ at h
  rw [he] at h
  exact h

private theorem normalizedMate_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {Lb : C ⥤ D} {Rb : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a : L ⊣ R) (b : Lb ⊣ Rb)
    (e : L ⋙ H ≅ G ⋙ Lb) (r : R ⋙ G ≅ H ⋙ Rb)
    (hm : (mateEquiv a b e.inv).natTrans = r.hom) (M : A) :
    b.unit.app (G.obj M) = G.map (a.unit.app M) ≫ r.hom.app (L.obj M) ≫
      Rb.map (e.hom.app M) := by
  have h := unit_mateEquiv a b e.inv M
  change G.map (a.unit.app M) ≫ (mateEquiv a b e.inv).natTrans.app (L.obj M) = _ at h
  rw [hm] at h
  apply (cancel_mono (Rb.map (e.inv.app M))).mp
  simp only [Category.assoc, ← Rb.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact h.symm

private theorem normalizedMate_counit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {Lb : C ⥤ D} {Rb : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a : L ⊣ R) (b : Lb ⊣ Rb)
    (e : L ⋙ H ≅ G ⋙ Lb) (r : R ⋙ G ≅ H ⋙ Rb)
    (hm : (mateEquiv a b e.inv).natTrans = r.hom) (N : B) :
    Lb.map (r.hom.app N) ≫ b.counit.app (H.obj N) =
      e.inv.app (R.obj N) ≫ H.map (a.counit.app N) := by
  have h := mateEquiv_counit a b e.inv N
  change Lb.map ((mateEquiv a b e.inv).natTrans.app N) ≫ _ = _ at h
  rw [hm] at h
  exact h

private theorem unit_of_inverse_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {Lb : C ⥤ D} {Rb : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a : L ⊣ R) (b : Lb ⊣ Rb)
    (e : L ⋙ H ≅ G ⋙ Lb) (r : R ⋙ G ≅ H ⋙ Rb) (M : A)
    (h : b.unit.app (G.obj M) ≫ Rb.map (e.inv.app M) =
      G.map (a.unit.app M) ≫ r.hom.app (L.obj M)) :
    b.unit.app (G.obj M) = G.map (a.unit.app M) ≫ r.hom.app (L.obj M) ≫
      Rb.map (e.hom.app M) := by
  apply (cancel_mono (Rb.map (e.inv.app M))).mp
  simp only [Category.assoc, ← Rb.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact h

private theorem transport_unit_right
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R R₀ : B ⥤ A} {Lb : C ⥤ D} {Rb : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a : L ⊣ R) (b : Lb ⊣ Rb)
    (e : L ⋙ H ≅ G ⋙ Lb) (r : R ⋙ G ≅ H ⋙ Rb) (s : R₀ ≅ R) (M : A)
    (h : b.unit.app (G.obj M) = G.map (a.unit.app M) ≫ r.hom.app (L.obj M) ≫
      Rb.map (e.hom.app M)) :
    b.unit.app (G.obj M) = G.map ((a.ofNatIsoRight s.symm).unit.app M) ≫
      (Functor.isoWhiskerRight s G ≪≫ r).hom.app (L.obj M) ≫
      Rb.map (e.hom.app M) := by
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.map_comp, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc]
  rw [← G.map_comp_assoc (s.inv.app (L.obj M)) (s.hom.app (L.obj M)),
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact h

private theorem mate_of_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {Lb : C ⥤ D} {Rb : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a : L ⊣ R) (b : Lb ⊣ Rb)
    (e : L ⋙ H ≅ G ⋙ Lb) (r : R ⋙ G ≅ H ⋙ Rb)
    (hu : ∀ M, b.unit.app (G.obj M) =
      G.map (a.unit.app M) ≫ r.hom.app (L.obj M) ≫ Rb.map (e.hom.app M)) :
    (mateEquiv a b e.inv).natTrans = r.hom := by
  change mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv) = TwoSquare.mk _ _ _ _ r.hom
  apply (mateEquiv a b).symm.injective
  rw [Equiv.symm_apply_apply]
  apply TwoSquare.ext
  intro M
  change e.inv.app M = ((mateEquiv a b).symm r.hom).app M
  apply (b.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  calc
    _ = G.map (a.unit.app M) ≫ r.hom.app (L.obj M) := by
      rw [hu M]
      simp only [Category.assoc, ← Rb.map_comp, Iso.hom_inv_id_app]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
    _ = _ := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ r.hom) M

private theorem scalar_map {R : Type*} [Ring R] {M N : ModuleCat R}
    (f : M ⟶ N) (r : R) (m m' : M) (h : r • m = m') :
    r • f m = f m' :=
  (f.hom.map_smul r m).symm.trans (congrArg f h)

section ExactUnits

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

private theorem exact_unit_fac
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) (K : CochainComplex A ℤ) :
    a.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  have hu : a.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
    simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_unit_app]
    rfl
  rw [hu]
  simp only [Category.assoc, ← G.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [G.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exact_homotopy_unit_fac
    {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) (K : HomotopyCategory A (.up ℤ)) :
    a.mapExactDerivedCategory.unit.app (DerivedCategory.Qh.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    F.mapDerivedCategoryFactorsh_hom_app, G.mapDerivedCategoryFactorsh_hom_app]
  dsimp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Functor.comp_obj, HomotopyCategory.quotient_obj_as]
  simp only [Functor.map_comp, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.assoc]
  erw [← a.mapExactDerivedCategory.unit.naturality_assoc]
  simp only [Functor.id_map, ← G.mapDerivedCategory.map_comp_assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  erw [reassoc_of% exact_unit_fac a K]
  erw [← DerivedCategory.quotientCompQhIso_hom_naturality_assoc,
    Iso.hom_inv_id_app, Category.comp_id]

end ExactUnits

private theorem squareSymm
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : A ⥤ B} {H : B ⥤ D} {G : A ⥤ C} {Lb : C ⥤ D}
    [L.Additive] [H.Additive] [G.Additive] [Lb.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits Lb] [PreservesFiniteColimits Lb]
    (e : L ⋙ H ≅ G ⋙ Lb) :
    Functor.mapDerivedCategorySquareIso e.symm =
      (Functor.mapDerivedCategorySquareIso e).symm := by
  apply Iso.ext
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

variable [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]

/-- Localize the specified internal ordinary open adjunction termwise, then express
its right adjoint through the canonical exact left-derived comparison.
Source: Stacks 015F and 03DJ
(blueprint: lem-pd-section-derived-open-adjunction-normalization). -/
def localizedInternalOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : internalDerivedExtension Λ j ⊣ internalDerivedPullback Λ j :=
  (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)).ofNatIsoRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ j).symm

/-- Localize the specified section-module ordinary open adjunction independently.
Its restriction is the exact levelwise realization of the ringed left derived pullback.
Source: Stacks 015F and 03DJ
(blueprint: lem-pd-section-derived-open-adjunction-normalization). -/
def localizedSectionOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : derivedExtension Λ j ⊣ derivedPullback Λ j :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction (openAdjunction Λ j)

private theorem internal_exact_adjunction_eq {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
      (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)) =
    Adjunction.mapDerivedCategoryAdjunction
      (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j) := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso (internalModules Λ U) (.up ℤ))
  intro K
  apply (cancel_mono
    ((CondensedRing.upperStar Λ j).mapDerivedCategory.map
        ((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategoryFactorsh.hom.app K) ≫
      (CondensedRing.upperStar Λ j).mapDerivedCategoryFactorsh.hom.app
        (((CondensedRing.openImmersionLowerShriek Λ j).mapHomotopyCategory (.up ℤ)).obj K))).mp
  exact (exact_homotopy_unit_fac
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j) K).trans
      (Adjunction.mapDerivedCategoryAdjunction_unit_app_Qh_obj
        (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j) K).symm

private theorem section_exact_adjunction_eq {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    localizedSectionOpenAdjunction Λ j = (openAdjunction Λ j).mapDerivedCategoryAdjunction := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso (modules Λ U) (.up ℤ))
  intro K
  apply (cancel_mono
    ((pullback Λ j).mapDerivedCategory.map
        ((extension Λ j).mapDerivedCategoryFactorsh.hom.app K) ≫
      (pullback Λ j).mapDerivedCategoryFactorsh.hom.app
        (((extension Λ j).mapHomotopyCategory (.up ℤ)).obj K))).mp
  exact (exact_homotopy_unit_fac (openAdjunction Λ j) K).trans
    ((openAdjunction Λ j).mapDerivedCategoryAdjunction_unit_app_Qh_obj K).symm

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
private theorem ordinary_open_mate {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (mateEquiv (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)
      (openAdjunction Λ j) (ordinaryExtensionComparison Λ j).inv).natTrans =
        (pullComparison Λ j).hom := by
  unfold ordinaryExtensionComparison InternalModuleOperations.openComparison
  exact (InternalModuleOperations.openComparison_existsUnique Λ j).exists.choose_spec

private theorem derived_open_unit {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (K : DerivedCategory (internalModules Λ U)) :
    (localizedSectionOpenAdjunction Λ j).unit.app ((derivedEquivalence Λ U).functor.obj K) =
      (derivedEquivalence Λ U).functor.map
          ((localizedInternalOpenAdjunction Λ j).unit.app K) ≫
        (derivedPullComparison Λ j).hom.app ((internalDerivedExtension Λ j).obj K) ≫
        (derivedPullback Λ j).map ((derivedExtensionComparison Λ j).hom.app K) := by
  have hm := ordinary_open_mate Λ j
  have h := Adjunction.mapDerivedCategoryAdjunction_mate
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j)
    (openAdjunction Λ j) (pullComparison Λ j)
    (ordinaryExtensionComparison Λ j).symm (fun F ↦ by
      simp only [Iso.symm_hom]
      rw [normalizedMate_unit _ _ _ _ hm F]
      simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]) K
  rw [← internal_exact_adjunction_eq Λ j, ← section_exact_adjunction_eq Λ j,
    squareSymm] at h
  have hu := unit_of_inverse_unit
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
      (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j))
    (localizedSectionOpenAdjunction Λ j)
    (Functor.mapDerivedCategorySquareIso (ordinaryExtensionComparison Λ j))
    (Functor.mapDerivedCategorySquareIso (pullComparison Λ j)) K h
  exact transport_unit_right
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
      (CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j))
    (localizedSectionOpenAdjunction Λ j)
    (Functor.mapDerivedCategorySquareIso (ordinaryExtensionComparison Λ j))
    (Functor.mapDerivedCategorySquareIso (pullComparison Λ j))
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ j) K hu

private theorem derived_open_mate {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (mateEquiv (localizedInternalOpenAdjunction Λ j) (localizedSectionOpenAdjunction Λ j)
      (derivedExtensionComparison Λ j).inv).natTrans = (derivedPullComparison Λ j).hom := by
  exact mate_of_unit _ _ _ _ (derived_open_unit Λ j)

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
private theorem scalar_normalization {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ (F : internalModules Λ U) (V : U.ProEt)
      (r : (ring Λ X).obj.obj (op (openSectionObject j V)))
      (m : ((equivalence Λ U).functor.obj F).val.obj (op V)),
      r • internalOpenGenerator Λ j F V m =
        internalOpenGenerator Λ j F V (openCoefficientSection Λ j V r • m) ∧
      r • ((ordinaryExtensionComparison Λ j).hom.app F).val.app
          (op (openSectionObject j V)) (internalOpenGenerator Λ j F V m) =
        ((ordinaryExtensionComparison Λ j).hom.app F).val.app
          (op (openSectionObject j V))
          (internalOpenGenerator Λ j F V (openCoefficientSection Λ j V r • m))) := by
  intro F V r m
  have h := sectionOpenGenerator_scalar Λ j F V r m
  exact ⟨h, scalar_map
    (((ordinaryExtensionComparison Λ j).hom.app F).val.app
      (op (openSectionObject j V))) r _ _ h⟩

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
private theorem ordinary_hom_normalization {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ (F : internalModules Λ U) (G : internalModules Λ X)
      (q : (CondensedRing.openImmersionLowerShriek Λ j).obj F ⟶ G),
      (openAdjunction Λ j).homEquiv _ _
          ((ordinaryExtensionComparison Λ j).inv.app F ≫
            (equivalence Λ X).functor.map q) =
        (equivalence Λ U).functor.map
            ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv _ _ q) ≫
          (pullComparison Λ j).hom.app G) := by
  exact normalizedMate_hom
    (G := (equivalence Λ U).functor) (H := (equivalence Λ X).functor)
    _ _ _ _ (ordinary_open_mate Λ j)

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
private theorem ordinary_unit_normalization {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ F : internalModules Λ U,
      (openAdjunction Λ j).unit.app ((equivalence Λ U).functor.obj F) =
        (equivalence Λ U).functor.map
            ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).unit.app F) ≫
          (pullComparison Λ j).hom.app ((CondensedRing.openImmersionLowerShriek Λ j).obj F) ≫
          (pullback Λ j).map ((ordinaryExtensionComparison Λ j).hom.app F)) := by
  exact normalizedMate_unit
    (G := (equivalence Λ U).functor) (H := (equivalence Λ X).functor)
    _ _ _ _ (ordinary_open_mate Λ j)

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
private theorem ordinary_counit_normalization {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ G : internalModules Λ X,
      (extension Λ j).map ((pullComparison Λ j).hom.app G) ≫
          (openAdjunction Λ j).counit.app ((equivalence Λ X).functor.obj G) =
        (ordinaryExtensionComparison Λ j).inv.app ((CondensedRing.upperStar Λ j).obj G) ≫
          (equivalence Λ X).functor.map
            ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app G)) := by
  exact normalizedMate_counit
    (G := (equivalence Λ U).functor) (H := (equivalence Λ X).functor)
    _ _ _ _ (ordinary_open_mate Λ j)

private theorem derived_hom_normalization {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ (K : DerivedCategory (internalModules Λ U))
      (M : DerivedCategory (internalModules Λ X))
      (q : (internalDerivedExtension Λ j).obj K ⟶ M),
      (localizedSectionOpenAdjunction Λ j).homEquiv _ _
          ((derivedExtensionComparison Λ j).inv.app K ≫
            (derivedEquivalence Λ X).functor.map q) =
        (derivedEquivalence Λ U).functor.map
            ((localizedInternalOpenAdjunction Λ j).homEquiv _ _ q) ≫
          (derivedPullComparison Λ j).hom.app M) := by
  exact normalizedMate_hom
    (G := (derivedEquivalence Λ U).functor) (H := (derivedEquivalence Λ X).functor)
    _ _ _ _ (derived_open_mate Λ j)

private theorem derived_counit_normalization {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ M : DerivedCategory (internalModules Λ X),
      (derivedExtension Λ j).map ((derivedPullComparison Λ j).hom.app M) ≫
          (localizedSectionOpenAdjunction Λ j).counit.app
            ((derivedEquivalence Λ X).functor.obj M) =
        (derivedExtensionComparison Λ j).inv.app ((internalDerivedPullback Λ j).obj M) ≫
          (derivedEquivalence Λ X).functor.map
            ((localizedInternalOpenAdjunction Λ j).counit.app M)) := by
  exact normalizedMate_counit
    (G := (derivedEquivalence Λ U).functor) (H := (derivedEquivalence Λ X).functor)
    _ _ _ _ (derived_open_mate Λ j)

/-- The fixed extension comparison identifies the scalar actions, ordinary Hom
bijections, exactness and independently localized derived open adjunctions.
Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ; Derived Categories,
Tag 015F (blueprint: lem-pd-section-derived-open-adjunction-normalization).

Proof, following the ten steps of the node.
1. Identify the open pro-etale site with the localized ambient site using Part (1)
   of weakly-etale localization. Use alpha_j, not the constant-ring comparisons.
   Pullback is restriction followed by scalar extension; a tensor a tensor m maps
   to a times m and the inverse sends m to 1 tensor m.
2. The abelian open adjunction identifies the underlying extension sheaves by
   sending each direct-sum generator to the same generator. Its unit is precisely
   internalOpenGenerator, the sheafified summand injection.
3. The projection-formula map sends iota_phi(r| tensor m) to r tensor iota_phi(m).
   Its inverse followed by the action therefore sends r tensor iota_phi(m) to
   iota_phi(alpha_j(r|) m). Module sheafification extends this action uniquely.
   This proves linearity of the generator comparison and both scalar equations.
4. Both ordinary Hom maps send q to m mapping to q(iota_phi(m)). Conversely each
   linear map on the slice extends uniquely through the sum and sheafification.
   They are inverse on generators, proving the ordinary Hom identity for the
   uniquely mate-normalized comparison of SectionModuleOperationsData.
5. Substitute identity and counit into that identity to obtain the two displayed
   ordinary unit and counit equations.
6. Exactness on the section side follows from localizedSystemExact and change of
   coefficients along alpha_j. Internal extension and pullback are exact by their
   defining results. The fixed section equivalences are exact. No boundedness or
   injectivity hypothesis is imposed.
7. Exact-functor factorization localizes all complexes termwise. Localize the
   ordinary adjunctions with exactDerivedAdjunction and localize their comparisons.
   The localization universal property preserves the comparison equations.
8. The resolution comparison equation in sectionDerivedPushpullNormalization
   identifies derivedPullComparison with the localized ordinary pull comparison,
   after the two exact left-derived identifications. Cancel their invertible
   resolution maps on every complex; localization gives the equality everywhere.
9. Localize Step 5's unit and counit equations and rewrite the right adjoints by
   Step 8. These are the independently localized adjunctions defined above.
10. Expand the section Hom map as R'(q) composed with its unit, insert Step 9,
    cancel R'(c inverse) against R'(c), and use naturality of b. The result is
    b composed with D(E_U) of the internal Hom map for arbitrary derived q.
    Step 9 also gives the final derived counit equation.
-/
theorem sectionDerivedOpenAdjunctionNormalization {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ (F : internalModules Λ U) (V : U.ProEt)
      (r : (ring Λ X).obj.obj (op (openSectionObject j V)))
      (m : ((equivalence Λ U).functor.obj F).val.obj (op V)),
      r • internalOpenGenerator Λ j F V m =
        internalOpenGenerator Λ j F V (openCoefficientSection Λ j V r • m) ∧
      r • ((ordinaryExtensionComparison Λ j).hom.app F).val.app
          (op (openSectionObject j V)) (internalOpenGenerator Λ j F V m) =
        ((ordinaryExtensionComparison Λ j).hom.app F).val.app
          (op (openSectionObject j V))
          (internalOpenGenerator Λ j F V (openCoefficientSection Λ j V r • m))) ∧
    (∀ (F : internalModules Λ U) (G : internalModules Λ X)
      (q : (CondensedRing.openImmersionLowerShriek Λ j).obj F ⟶ G),
      (openAdjunction Λ j).homEquiv _ _
          ((ordinaryExtensionComparison Λ j).inv.app F ≫
            (equivalence Λ X).functor.map q) =
        (equivalence Λ U).functor.map
            ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).homEquiv _ _ q) ≫
          (pullComparison Λ j).hom.app G) ∧
    (∀ F : internalModules Λ U,
      (openAdjunction Λ j).unit.app ((equivalence Λ U).functor.obj F) =
        (equivalence Λ U).functor.map
            ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).unit.app F) ≫
          (pullComparison Λ j).hom.app ((CondensedRing.openImmersionLowerShriek Λ j).obj F) ≫
          (pullback Λ j).map ((ordinaryExtensionComparison Λ j).hom.app F)) ∧
    (∀ G : internalModules Λ X,
      (extension Λ j).map ((pullComparison Λ j).hom.app G) ≫
          (openAdjunction Λ j).counit.app ((equivalence Λ X).functor.obj G) =
        (ordinaryExtensionComparison Λ j).inv.app ((CondensedRing.upperStar Λ j).obj G) ≫
          (equivalence Λ X).functor.map
            ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app G)) ∧
    PreservesFiniteLimits (CondensedRing.openImmersionLowerShriek Λ j) ∧
    PreservesFiniteColimits (CondensedRing.openImmersionLowerShriek Λ j) ∧
    PreservesFiniteLimits (CondensedRing.upperStar Λ j) ∧
    PreservesFiniteColimits (CondensedRing.upperStar Λ j) ∧
    PreservesFiniteLimits (extension Λ j) ∧
    PreservesFiniteColimits (extension Λ j) ∧
    PreservesFiniteLimits (pullback Λ j) ∧
    PreservesFiniteColimits (pullback Λ j) ∧
    (∀ (K : DerivedCategory (internalModules Λ U))
      (M : DerivedCategory (internalModules Λ X))
      (q : (internalDerivedExtension Λ j).obj K ⟶ M),
      (localizedSectionOpenAdjunction Λ j).homEquiv _ _
          ((derivedExtensionComparison Λ j).inv.app K ≫
            (derivedEquivalence Λ X).functor.map q) =
        (derivedEquivalence Λ U).functor.map
            ((localizedInternalOpenAdjunction Λ j).homEquiv _ _ q) ≫
          (derivedPullComparison Λ j).hom.app M) ∧
    (∀ K : DerivedCategory (internalModules Λ U),
      (localizedSectionOpenAdjunction Λ j).unit.app ((derivedEquivalence Λ U).functor.obj K) =
        (derivedEquivalence Λ U).functor.map
            ((localizedInternalOpenAdjunction Λ j).unit.app K) ≫
          (derivedPullComparison Λ j).hom.app ((internalDerivedExtension Λ j).obj K) ≫
          (derivedPullback Λ j).map ((derivedExtensionComparison Λ j).hom.app K)) ∧
    (∀ M : DerivedCategory (internalModules Λ X),
      (derivedExtension Λ j).map ((derivedPullComparison Λ j).hom.app M) ≫
          (localizedSectionOpenAdjunction Λ j).counit.app
            ((derivedEquivalence Λ X).functor.obj M) =
        (derivedExtensionComparison Λ j).inv.app ((internalDerivedPullback Λ j).obj M) ≫
          (derivedEquivalence Λ X).functor.map
            ((localizedInternalOpenAdjunction Λ j).counit.app M)) := by
  -- Use the mate-normalized comparison and exact localization directly.
  exact ⟨scalar_normalization Λ j, ordinary_hom_normalization Λ j,
    ordinary_unit_normalization Λ j, ordinary_counit_normalization Λ j,
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    derived_hom_normalization Λ j, derived_open_unit Λ j, derived_counit_normalization Λ j⟩

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
