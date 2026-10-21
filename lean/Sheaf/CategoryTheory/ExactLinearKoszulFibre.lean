/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.CategoryTheory.SignedKoszulCompletionModel
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Sheaf.CategoryTheory.SignedKoszulModelExists

/-!
# Exact linear functors and the signed Koszul completion fibre

Source: Stacks Project, algebraization.tex, Tag 0A0E, and the final paragraph of the
blueprint proof lem-cbc-completed-extension-zero-comparison, refined by the explicit
signed calculation of the DAG (blueprint: lem-cbc-exact-linear-koszul-fiber).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v uH vH z wR wS

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The canonical signed Koszul comparison, together with its localization and unit equations.
All maps are specified by their finite, countable, and binary projections. This structure
packages the conclusions; it adds no hypothesis or choice of an unspecified cone map.
Source: Stacks Tag 0A0E and the signed-model refinement in the blueprint proof of
lem-cbc-completed-extension-zero-comparison (blueprint: lem-cbc-exact-linear-koszul-fiber). -/
structure SignedKoszulFibreComparison
    {ER : Type u} [Category.{uH} ER] [Abelian ER]
    [HasFiniteBiproducts ER] [HasBinaryBiproducts ER]
    {ES : Type v} [Category.{vH} ES] [Abelian ES]
    [HasFiniteBiproducts ES] [HasBinaryBiproducts ES]
    [HasDerivedCategory.{wR} ER] [HasDerivedCategory.{wS} ES]
    {A : Type z} [CommRing A]
    {σR : ∀ {X Y : ER}, A → (X ⟶ Y) → (X ⟶ Y)}
    {σS : ∀ {X Y : ES}, A → (X ⟶ Y) → (X ⟶ Y)}
    {r : ℕ} {a : Fin r → A}
    {TR : ℕ → CochainComplex ER ℤ ⥤ CochainComplex ER ℤ}
    {TS : ℕ → CochainComplex ES ℤ ⥤ CochainComplex ES ℤ}
    (F : ER ⥤ ES) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (MR : SignedKoszulCompletionModel A ER σR a TR)
    (MS : SignedKoszulCompletionModel A ES σS a TS) where
  /-- The finite-coordinate comparison. -/
  alpha : ∀ m : ℕ,
      TR m ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ TS m
  /-- The countable-product comparison. -/
  beta : MR.product ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ MS.product
  /-- The signed-fibre comparison. -/
  h : MR.fibre ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ MS.fibre
  /-- The induced source completion functor. -/
  HR : DerivedCategory ER ⥤ DerivedCategory ER
  /-- The induced target completion functor. -/
  HS : DerivedCategory ES ⥤ DerivedCategory ES
  /-- Its source localization factorization. -/
  eR : DerivedCategory.Q ⋙ HR ≅ MR.fibre ⋙ DerivedCategory.Q
  /-- Its target localization factorization. -/
  eS : DerivedCategory.Q ⋙ HS ≅ MS.fibre ⋙ DerivedCategory.Q
  /-- The localized source unit. -/
  etaR : 𝟭 (DerivedCategory ER) ⟶ HR
  /-- The localized target unit. -/
  etaS : 𝟭 (DerivedCategory ES) ⟶ HS
  /-- The descended comparison. -/
  hd : HR ⋙ F.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ HS
  /-- Every finite projection is the image of the specified tensor projection. -/
  alpha_coordinates : ∀ (m : ℕ) (K : CochainComplex ER ℤ) (q : ℤ) (I : Finset (Fin r)),
    ((alpha m).hom.app K).f q ≫
        (MS.coordinates m ((F.mapHomologicalComplex (.up ℤ)).obj K) q).hom ≫
          biproduct.π _ I =
      F.map ((MR.coordinates m K q).hom ≫ biproduct.π _ I)
  /-- Every tower projection is the image projection followed by alpha. -/
  beta_projection : ∀ (m : ℕ) (K : CochainComplex ER ℤ),
    beta.hom.app K ≫ (MS.projection m).app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      (F.mapHomologicalComplex (.up ℤ)).map ((MR.projection m).app K) ≫
        (alpha m).hom.app K
  /-- The first fibre projection is beta after the canonical binary comparison. -/
  h_fst : ∀ (K : CochainComplex ER ℤ) (q : ℤ),
    (h.hom.app K).f q ≫
        (MS.fibreCoordinates ((F.mapHomologicalComplex (.up ℤ)).obj K) q).hom ≫
          biprod.fst =
      F.map ((MR.fibreCoordinates K q).hom ≫ biprod.fst) ≫
        (beta.hom.app K).f q
  /-- The second fibre projection is beta in degree q-1. -/
  h_snd : ∀ (K : CochainComplex ER ℤ) (q : ℤ),
    (h.hom.app K).f q ≫
        (MS.fibreCoordinates ((F.mapHomologicalComplex (.up ℤ)).obj K) q).hom ≫
          biprod.snd =
      F.map ((MR.fibreCoordinates K q).hom ≫ biprod.snd) ≫
        (beta.hom.app K).f (q - 1)
  /-- The strict chain comparison carries the specified unit to the specified unit. -/
  unit_compatibility : ∀ K : CochainComplex ER ℤ,
    (F.mapHomologicalComplex (.up ℤ)).map (MR.unit.app K) ≫ h.hom.app K =
      MS.unit.app ((F.mapHomologicalComplex (.up ℤ)).obj K)
  /-- The source derived unit is the localization of the chain unit. -/
  etaR_factor : ∀ K : CochainComplex ER ℤ,
    etaR.app (DerivedCategory.Q.obj K) ≫ eR.hom.app K =
      DerivedCategory.Q.map (MR.unit.app K)
  /-- The target derived unit is the localization of the chain unit. -/
  etaS_factor : ∀ K : CochainComplex ES ℤ,
    etaS.app (DerivedCategory.Q.obj K) ≫ eS.hom.app K =
      DerivedCategory.Q.map (MS.unit.app K)
  /-- The derived comparison is the localization of the chain comparison. -/
  derived_factor : ∀ K : CochainComplex ER ℤ,
    F.mapDerivedCategory.map (eR.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app (MR.fibre.obj K) ≫
          DerivedCategory.Q.map (h.hom.app K) =
      hd.hom.app (DerivedCategory.Q.obj K) ≫
        HS.map (F.mapDerivedCategoryFactors.hom.app K) ≫
          eS.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K)
  /-- The descended comparison carries the source unit to the target unit. -/
  derived_unit : ∀ X : DerivedCategory ER,
    F.mapDerivedCategory.map (etaR.app X) ≫ hd.hom.app X =
      etaS.app (F.mapDerivedCategory.obj X)
  /-- Invertibility of the source derived unit implies that of the target unit. -/
  preserves_unit_isIso : ∀ X : DerivedCategory ER,
    IsIso (etaR.app X) → IsIso (etaS.app (F.mapDerivedCategory.obj X))

/-- The preceding comparison specialized to the actual sheaf Koszul tensors and their
pure-tensor-normalized coordinates; all conclusion fields are inherited transparently.
Source: Stacks Tag 0A0E (blueprint: lem-cbc-exact-linear-koszul-fiber). -/
abbrev ExactLinearSignedKoszulFibreComparison
    {C : Type u} [SmallCategory C] {D : Type v} [SmallCategory D]
    {J : GrothendieckTopology C} {L : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf L CommRingCat.{v})
    {A : Type z} [CommRing A]
    (ρR : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    (ρS : A →+* RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
    [HasDerivedCategory.{wR} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{v}
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))]
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{v} ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {r : ℕ} {a : Fin r → A}
    (MR : RingedSignedKoszulCompletionModel R ρR a)
    (MS : RingedSignedKoszulCompletionModel S ρS a) :=
  letI := Abelian.hasFiniteBiproducts (C := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  letI := Abelian.hasFiniteBiproducts (C := ringedSiteModules.{v}
    ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))
  SignedKoszulFibreComparison F MR.model MS.model

namespace SignedKoszulComparisonAux

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe cu cv du dv cw dw

section ChainComparison

variable {E : Type cu} [Category.{cv} E] [Abelian E]
  {D : Type du} [Category.{dv} D] [Abelian D]
  [HasFiniteBiproducts E] [HasFiniteBiproducts D]
variable (F : E ⥤ D) [F.Additive]
private def finiteCompare {ι : Type} [Fintype ι] (P : ι → E)
    {X : E} {Y : D} (e : X ≅ ⨁ P) (f : Y ≅ ⨁ fun i ↦ F.obj (P i)) :
    F.obj X ≅ Y := F.mapIso e ≪≫ F.mapBiproduct P ≪≫ f.symm
omit [HasFiniteBiproducts D] in
private theorem finiteCompare_proj {ι : Type} [Fintype ι] (P : ι → E)
    {X : E} {Y : D} (e : X ≅ ⨁ P) (f : Y ≅ ⨁ fun i ↦ F.obj (P i)) (i : ι) :
    (finiteCompare F P e f).hom ≫ f.hom ≫ biproduct.π _ i =
      F.map (e.hom ≫ biproduct.π _ i) := by
  simp only [finiteCompare, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, F.mapBiproduct_hom, biproduct.lift_π,
    ← F.map_comp]
omit [HasFiniteBiproducts D] in
@[reassoc] private theorem finiteCompare_incl {ι : Type} [Fintype ι] (P : ι → E)
    {X : E} {Y : D} (e : X ≅ ⨁ P) (f : Y ≅ ⨁ fun i ↦ F.obj (P i)) (i : ι) :
    F.map (biproduct.ι P i ≫ e.inv) ≫ (finiteCompare F P e f).hom =
      biproduct.ι _ i ≫ f.inv := by
  simp only [finiteCompare, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    F.map_comp, Category.assoc, ← F.map_comp_assoc, e.inv_hom_id, Category.comp_id,
    F.mapBiproduct_hom]
  apply (cancel_mono f.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply biproduct.hom_ext
  intro j
  classical
  simp [Category.assoc, ← F.map_comp, biproduct.ι_π, eqToHom_map]
omit [HasFiniteBiproducts D] in
private theorem finiteCompare_matrix {ι κ : Type} [Fintype ι] [Fintype κ]
    (P : ι → E) (Q : κ → E) {X X' : E} {Y Y' : D}
    (e : X ≅ ⨁ P) (e' : X' ≅ ⨁ Q)
    (f : Y ≅ ⨁ fun i ↦ F.obj (P i)) (f' : Y' ≅ ⨁ fun j ↦ F.obj (Q j))
    (a : X ⟶ X') (b : Y ⟶ Y')
    (h : ∀ i j,
      F.map (biproduct.ι P i ≫ e.inv ≫ a ≫ e'.hom ≫ biproduct.π Q j) =
        biproduct.ι _ i ≫ f.inv ≫ b ≫ f'.hom ≫ biproduct.π _ j) :
    (finiteCompare F P e f).hom ≫ b = F.map a ≫ (finiteCompare F Q e' f').hom := by
  apply (cancel_mono f'.hom).mp
  apply biproduct.hom_ext
  intro j
  simp only [Category.assoc, finiteCompare_proj]
  apply (cancel_epi (F.map e.inv)).mp
  apply (cancel_epi (F.mapBiproduct P).inv).mp
  apply biproduct.hom_ext'
  intro i
  simp only [F.mapBiproduct_inv, biproduct.ι_desc_assoc]
  rw [← F.map_comp_assoc, finiteCompare_incl_assoc]
  simpa only [Category.assoc, ← F.map_comp] using (h i j).symm

variable {A : Type z} [CommRing A]
  {σE : ∀ {X Y : E}, A → (X ⟶ Y) → (X ⟶ Y)}
  {σD : ∀ {X Y : D}, A → (X ⟶ Y) → (X ⟶ Y)}
  {r : ℕ} {a : Fin r → A}
  {TE : ℕ → CochainComplex E ℤ ⥤ CochainComplex E ℤ}
  {TD : ℕ → CochainComplex D ℤ ⥤ CochainComplex D ℤ}
  (ME : SignedKoszulCompletionModel A E σE a TE)
  (MD : SignedKoszulCompletionModel A D σD a TD)
  (hlinear : ∀ {X Y : E} (b : A) (f : X ⟶ Y), F.map (σE b f) = σD b (F.map f))
omit [HasFiniteBiproducts E] [HasFiniteBiproducts D] in
private theorem mapXIso (K : CochainComplex E ℤ) {i j : ℤ} (h : i = j) :
    F.map (K.XIsoOfEq h).hom =
      (((F.mapHomologicalComplex (.up ℤ)).obj K).XIsoOfEq h).hom := by
  subst j
  exact F.map_id _
private def alphaX (m : ℕ) (K : CochainComplex E ℤ) (q : ℤ) :
    F.obj (((TE m).obj K).X q) ≅
      ((TD m).obj ((F.mapHomologicalComplex (.up ℤ)).obj K)).X q :=
  finiteCompare F (fun I : Finset (Fin r) ↦ K.X (q + I.card))
    (ME.coordinates m K q) (MD.coordinates m ((F.mapHomologicalComplex (.up ℤ)).obj K) q)
include hlinear in
private theorem alphaX_comm (m : ℕ) (K : CochainComplex E ℤ) (q : ℤ) :
    (alphaX F ME MD m K q).hom ≫
        ((TD m).obj ((F.mapHomologicalComplex (.up ℤ)).obj K)).d q (q + 1) =
      F.map (((TE m).obj K).d q (q + 1)) ≫ (alphaX F ME MD m K (q + 1)).hom := by
  apply finiteCompare_matrix
  intro I P
  have hd := MD.differential m ((F.mapHomologicalComplex (.up ℤ)).obj K) q I P
  simp only [Functor.mapHomologicalComplex_obj_X] at hd
  rw [ME.differential m K q I P, hd]
  split_ifs <;> simp only [Functor.map_add, Functor.map_zero, hlinear, mapXIso] <;> rfl
private def alphaObj (m : ℕ) (K : CochainComplex E ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj ((TE m).obj K) ≅
      (TD m).obj ((F.mapHomologicalComplex (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (alphaX F ME MD m K) (by
    intro i j h
    have hj : i + 1 = j := h
    subst j
    exact alphaX_comm F ME MD hlinear m K i)
private theorem alphaObj_natural (m : ℕ) {K L : CochainComplex E ℤ} (f : K ⟶ L) :
    (F.mapHomologicalComplex (.up ℤ)).map ((TE m).map f) ≫ (alphaObj F ME MD hlinear m L).hom =
      (alphaObj F ME MD hlinear m K).hom ≫
        (TD m).map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  apply HomologicalComplex.hom_ext
  intro q
  symm
  apply finiteCompare_matrix
  intro I P
  have hd := MD.map_coordinates m ((F.mapHomologicalComplex (.up ℤ)).map f) q I P
  simp only [Functor.mapHomologicalComplex_obj_X] at hd
  rw [ME.map_coordinates m f q I P, hd]
  split_ifs <;> simp [mapXIso]
private def alpha (m : ℕ) :
    TE m ⋙ F.mapHomologicalComplex (.up ℤ) ≅ F.mapHomologicalComplex (.up ℤ) ⋙ TD m :=
  NatIso.ofComponents (alphaObj F ME MD hlinear m) (alphaObj_natural F ME MD hlinear m)

private theorem alpha_step (m : ℕ) (K : CochainComplex E ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map ((ME.step m).app K) ≫
        (alpha F ME MD hlinear m).hom.app K =
      (alpha F ME MD hlinear (m + 1)).hom.app K ≫
        (MD.step m).app ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  apply HomologicalComplex.hom_ext
  intro q
  symm
  apply finiteCompare_matrix
  intro I P
  have hd := MD.step_coordinates m ((F.mapHomologicalComplex (.up ℤ)).obj K) q I P
  simp only [Functor.mapHomologicalComplex_obj_X] at hd
  rw [ME.step_coordinates m K q I P, hd]
  split_ifs <;> simp [hlinear, mapXIso]
@[reassoc] private theorem alpha_coordinates (m : ℕ) (K : CochainComplex E ℤ) (q : ℤ)
    (I : Finset (Fin r)) :
    (((alpha F ME MD hlinear m).hom.app K).f q) ≫
        (MD.coordinates m ((F.mapHomologicalComplex (.up ℤ)).obj K) q).hom ≫
          biproduct.π _ I =
      F.map ((ME.coordinates m K q).hom ≫ biproduct.π _ I) :=
  finiteCompare_proj F _ _ _ I
private theorem alpha_inclusion (m : ℕ) (K : CochainComplex E ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map ((ME.inclusion m).app K) ≫
        (alpha F ME MD hlinear m).hom.app K =
      (MD.inclusion m).app ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply (cancel_mono
    (MD.coordinates m ((F.mapHomologicalComplex (.up ℤ)).obj K) q).hom).mp
  apply biproduct.hom_ext
  intro I
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Category.assoc, alpha_coordinates, ← F.map_comp]
  rw [ME.inclusion_coordinates m K q I,
    MD.inclusion_coordinates m ((F.mapHomologicalComplex (.up ℤ)).obj K) q I]
  split_ifs <;> simp [mapXIso]
variable [HasCountableProducts E]
  [PreservesLimitsOfShape (Discrete ℕ) F]
private def mappedProductLimit (K : CochainComplex E ℤ) :
    IsLimit (Fan.mk ((F.mapHomologicalComplex (.up ℤ)).obj (ME.product.obj K))
      (fun m ↦ (F.mapHomologicalComplex (.up ℤ)).map ((ME.projection m).app K))) :=
  Fan.isLimitMapConeEquiv _ _ _ (isLimitOfPreserves _ (ME.isProduct K))
private def betaHom (K : CochainComplex E ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (ME.product.obj K) ⟶
      MD.product.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) :=
  Fan.IsLimit.lift (MD.isProduct _) (fun m ↦
    (F.mapHomologicalComplex (.up ℤ)).map ((ME.projection m).app K) ≫
      (alpha F ME MD hlinear m).hom.app K)
omit [HasCountableProducts E]
  [PreservesLimitsOfShape (Discrete ℕ) F] in
@[reassoc] private theorem betaHom_projection (K : CochainComplex E ℤ) (m : ℕ) :
    betaHom F ME MD hlinear K ≫ (MD.projection m).app _ =
      (F.mapHomologicalComplex (.up ℤ)).map ((ME.projection m).app K) ≫
        (alpha F ME MD hlinear m).hom.app K :=
  Fan.IsLimit.fac (MD.isProduct _) _ m
private def betaInv (K : CochainComplex E ℤ) :
    MD.product.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (F.mapHomologicalComplex (.up ℤ)).obj (ME.product.obj K) :=
  Fan.IsLimit.lift (mappedProductLimit F ME K) (fun m ↦
    (MD.projection m).app _ ≫ (alpha F ME MD hlinear m).inv.app K)
@[reassoc] private theorem betaInv_projection (K : CochainComplex E ℤ) (m : ℕ) :
    betaInv F ME MD hlinear K ≫
        (F.mapHomologicalComplex (.up ℤ)).map ((ME.projection m).app K) =
      (MD.projection m).app _ ≫ (alpha F ME MD hlinear m).inv.app K :=
  Fan.IsLimit.fac (mappedProductLimit F ME K) _ m
private def betaObj (K : CochainComplex E ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (ME.product.obj K) ≅
      MD.product.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) where
  hom := betaHom F ME MD hlinear K
  inv := betaInv F ME MD hlinear K
  hom_inv_id := by
    apply Fan.IsLimit.hom_ext (mappedProductLimit F ME K)
    intro m
    change (_ ≫ _) ≫ (F.mapHomologicalComplex (.up ℤ)).map ((ME.projection m).app K) =
      𝟙 _ ≫ (F.mapHomologicalComplex (.up ℤ)).map ((ME.projection m).app K)
    simp only [Category.assoc, betaInv_projection, betaHom_projection_assoc,
      Iso.hom_inv_id_app, Category.id_comp]
    exact Category.comp_id _
  inv_hom_id := by
    apply Fan.IsLimit.hom_ext (MD.isProduct _)
    intro m
    change (_ ≫ _) ≫ (MD.projection m).app _ = 𝟙 _ ≫ (MD.projection m).app _
    simp only [Category.assoc, betaHom_projection, betaInv_projection_assoc,
      Iso.inv_hom_id_app, Category.id_comp]
    exact Category.comp_id _
@[reassoc] private theorem beta_projection (m : ℕ) (K : CochainComplex E ℤ) :
    (betaObj F ME MD hlinear K).hom ≫ (MD.projection m).app _ =
      (F.mapHomologicalComplex (.up ℤ)).map ((ME.projection m).app K) ≫
        (alpha F ME MD hlinear m).hom.app K :=
  betaHom_projection F ME MD hlinear K m

private theorem betaObj_natural {K L : CochainComplex E ℤ} (f : K ⟶ L) :
    (F.mapHomologicalComplex (.up ℤ)).map (ME.product.map f) ≫
        (betaObj F ME MD hlinear L).hom =
      (betaObj F ME MD hlinear K).hom ≫
        MD.product.map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  apply Fan.IsLimit.hom_ext (MD.isProduct _)
  intro m
  change (_ ≫ _) ≫ (MD.projection m).app _ = (_ ≫ _) ≫ (MD.projection m).app _
  simp only [Category.assoc, (MD.projection m).naturality, beta_projection_assoc,
    beta_projection]
  have hn := (alpha F ME MD hlinear m).hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← hn]
  rw [← (F.mapHomologicalComplex (.up ℤ)).map_comp_assoc,
    (ME.projection m).naturality, (F.mapHomologicalComplex (.up ℤ)).map_comp, Category.assoc]
private def beta : ME.product ⋙ F.mapHomologicalComplex (.up ℤ) ≅
    F.mapHomologicalComplex (.up ℤ) ⋙ MD.product :=
  NatIso.ofComponents (betaObj F ME MD hlinear) (fun f ↦ betaObj_natural F ME MD hlinear f)
private theorem beta_shift (K : CochainComplex E ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (ME.shift.app K) ≫
        (beta F ME MD hlinear).hom.app K =
      (beta F ME MD hlinear).hom.app K ≫
        MD.shift.app ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  change (F.mapHomologicalComplex (.up ℤ)).map (ME.shift.app K) ≫
      (betaObj F ME MD hlinear K).hom = (betaObj F ME MD hlinear K).hom ≫ _
  apply Fan.IsLimit.hom_ext (MD.isProduct _)
  intro m
  change (_ ≫ _) ≫ (MD.projection m).app _ = (_ ≫ _) ≫ (MD.projection m).app _
  simp only [Category.assoc, MD.shift_projection, beta_projection_assoc, beta_projection]
  rw [← alpha_step, ← Functor.map_comp_assoc,
    ME.shift_projection, Functor.map_comp, Category.assoc]
private theorem beta_diagonal (K : CochainComplex E ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (ME.diagonal.app K) ≫
        (beta F ME MD hlinear).hom.app K =
      MD.diagonal.app ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  change (F.mapHomologicalComplex (.up ℤ)).map (ME.diagonal.app K) ≫
      (betaObj F ME MD hlinear K).hom = _
  apply Fan.IsLimit.hom_ext (MD.isProduct _)
  intro m
  change (_ ≫ _) ≫ (MD.projection m).app _ = _ ≫ (MD.projection m).app _
  rw [Category.assoc, beta_projection, ← Functor.map_comp_assoc,
    ME.diagonal_projection, MD.diagonal_projection, alpha_inclusion]

omit [HasCountableProducts E] in
@[reassoc] private theorem fibre_d_fst (K : CochainComplex E ℤ) (q : ℤ) :
    (ME.fibre.obj K).d q (q + 1) ≫ (ME.fibreCoordinates K (q + 1)).hom ≫ biprod.fst =
      (ME.fibreCoordinates K q).hom ≫ biprod.fst ≫ (ME.product.obj K).d q (q + 1) := by
  apply (cancel_epi (ME.fibreCoordinates K q).inv).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, biprod.lift_fst] using
    congrArg (fun t ↦ t ≫ biprod.fst) (ME.fibre_differential K q)
omit [HasCountableProducts E] in
@[reassoc] private theorem fibre_d_snd (K : CochainComplex E ℤ) (q : ℤ) :
    (ME.fibre.obj K).d q (q + 1) ≫ (ME.fibreCoordinates K (q + 1)).hom ≫ biprod.snd =
      (ME.fibreCoordinates K q).hom ≫ biprod.fst ≫ (𝟙 _ - (ME.shift.app K).f q) ≫
          ((ME.product.obj K).XIsoOfEq (Int.add_sub_cancel q 1).symm).hom -
        (ME.fibreCoordinates K q).hom ≫ biprod.snd ≫
          (ME.product.obj K).d (q - 1) ((q + 1) - 1) := by
  apply (cancel_epi (ME.fibreCoordinates K q).inv).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, biprod.lift_snd,
    Preadditive.comp_sub] using
    congrArg (fun t ↦ t ≫ biprod.snd) (ME.fibre_differential K q)
private def fibreX (K : CochainComplex E ℤ) (q : ℤ) :
    F.obj ((ME.fibre.obj K).X q) ≅
      (MD.fibre.obj ((F.mapHomologicalComplex (.up ℤ)).obj K)).X q := by
  letI := preservesBinaryBiproduct_of_preservesBiproduct F
    ((ME.product.obj K).X q) ((ME.product.obj K).X (q - 1))
  exact F.mapIso (ME.fibreCoordinates K q) ≪≫ F.mapBiprod _ _ ≪≫
    biprod.mapIso (HomologicalComplex.Hom.isoApp (betaObj F ME MD hlinear K) q)
      (HomologicalComplex.Hom.isoApp (betaObj F ME MD hlinear K) (q - 1)) ≪≫
    (MD.fibreCoordinates _ q).symm
@[reassoc] private theorem fibreX_fst (K : CochainComplex E ℤ) (q : ℤ) :
    (fibreX F ME MD hlinear K q).hom ≫
        (MD.fibreCoordinates ((F.mapHomologicalComplex (.up ℤ)).obj K) q).hom ≫
          biprod.fst =
      F.map ((ME.fibreCoordinates K q).hom ≫ biprod.fst) ≫
        ((betaObj F ME MD hlinear K).hom).f q := by
  simp only [fibreX, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, biprod.mapIso_hom, biprod.map_fst,
    Functor.mapBiprod_hom, biprod.lift_fst_assoc, Functor.mapIso_hom,
    ← F.map_comp_assoc]
  rfl
@[reassoc] private theorem fibreX_snd (K : CochainComplex E ℤ) (q : ℤ) :
    (fibreX F ME MD hlinear K q).hom ≫
        (MD.fibreCoordinates ((F.mapHomologicalComplex (.up ℤ)).obj K) q).hom ≫
          biprod.snd =
      F.map ((ME.fibreCoordinates K q).hom ≫ biprod.snd) ≫
        ((betaObj F ME MD hlinear K).hom).f (q - 1) := by
  simp only [fibreX, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, biprod.mapIso_hom, biprod.map_snd,
    Functor.mapBiprod_hom, biprod.lift_snd_assoc, Functor.mapIso_hom,
    ← F.map_comp_assoc]
  rfl

@[reassoc] private theorem beta_sub_shift (K : CochainComplex E ℤ) (q : ℤ) :
    ((betaObj F ME MD hlinear K).hom).f q ≫
        (𝟙 _ - (MD.shift.app ((F.mapHomologicalComplex (.up ℤ)).obj K)).f q) =
      F.map (𝟙 _ - (ME.shift.app K).f q) ≫ ((betaObj F ME MD hlinear K).hom).f q := by
  have hh := congrArg (fun f ↦ f.f q) (beta_shift F ME MD hlinear K)
  change F.map ((ME.shift.app K).f q) ≫ (betaObj F ME MD hlinear K).hom.f q =
    (betaObj F ME MD hlinear K).hom.f q ≫
      (MD.shift.app ((F.mapHomologicalComplex (.up ℤ)).obj K)).f q at hh
  simp only [Functor.map_sub, Functor.map_id, Preadditive.comp_sub,
    Preadditive.sub_comp, Category.comp_id, Category.id_comp, hh]
@[reassoc] private theorem beta_cast (K : CochainComplex E ℤ) {i j : ℤ} (hij : i = j) :
    ((betaObj F ME MD hlinear K).hom).f i ≫
        ((MD.product.obj ((F.mapHomologicalComplex (.up ℤ)).obj K)).XIsoOfEq hij).hom =
      F.map ((ME.product.obj K).XIsoOfEq hij).hom ≫
        ((betaObj F ME MD hlinear K).hom).f j := by
  subst j
  simp
private theorem fibreX_comm (K : CochainComplex E ℤ) (q : ℤ) :
    (fibreX F ME MD hlinear K q).hom ≫
        (MD.fibre.obj ((F.mapHomologicalComplex (.up ℤ)).obj K)).d q (q + 1) =
      F.map ((ME.fibre.obj K).d q (q + 1)) ≫
        (fibreX F ME MD hlinear K (q + 1)).hom := by
  apply (cancel_mono (MD.fibreCoordinates _ (q + 1)).hom).mp
  apply biprod.hom_ext
  · simp only [Category.assoc]
    rw [fibre_d_fst, fibreX_fst_assoc]
    rw [(betaObj F ME MD hlinear K).hom.comm q (q + 1)]
    rw [fibreX_fst, ← F.map_comp_assoc, fibre_d_fst]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  · simp only [Category.assoc]
    rw [fibre_d_snd, Preadditive.comp_sub (fibreX F ME MD hlinear K q).hom, fibreX_snd]
    rw [← F.map_comp_assoc, fibre_d_snd, F.map_sub,
      Preadditive.sub_comp _ _ ((betaObj F ME MD hlinear K).hom.f ((q + 1) - 1))]
    refine congrArg₂ (fun f g : F.obj ((ME.fibre.obj K).X q) ⟶
      (MD.product.obj ((F.mapHomologicalComplex (.up ℤ)).obj K)).X ((q + 1) - 1) ↦
        f - g) ?_ ?_
    · rw [fibreX_fst_assoc, beta_sub_shift_assoc, beta_cast]
      simp only [Functor.map_comp, Category.assoc]
    · rw [fibreX_snd_assoc, (betaObj F ME MD hlinear K).hom.comm]
      simp only [Functor.map_comp, Category.assoc]
      rfl

omit [HasCountableProducts E] in
@[reassoc] private theorem fibre_map_fst {K L : CochainComplex E ℤ} (f : K ⟶ L) (q : ℤ) :
    (ME.fibre.map f).f q ≫ (ME.fibreCoordinates L q).hom ≫ biprod.fst =
      (ME.fibreCoordinates K q).hom ≫ biprod.fst ≫ (ME.product.map f).f q := by
  apply (cancel_epi (ME.fibreCoordinates K q).inv).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, biprod.map_fst] using
    congrArg (fun t ↦ t ≫ biprod.fst) (ME.fibre_map f q)
omit [HasCountableProducts E] in
@[reassoc] private theorem fibre_map_snd {K L : CochainComplex E ℤ} (f : K ⟶ L) (q : ℤ) :
    (ME.fibre.map f).f q ≫ (ME.fibreCoordinates L q).hom ≫ biprod.snd =
      (ME.fibreCoordinates K q).hom ≫ biprod.snd ≫ (ME.product.map f).f (q - 1) := by
  apply (cancel_epi (ME.fibreCoordinates K q).inv).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, biprod.map_snd] using
    congrArg (fun t ↦ t ≫ biprod.snd) (ME.fibre_map f q)
private def fibreObj (K : CochainComplex E ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (ME.fibre.obj K) ≅
      MD.fibre.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fibreX F ME MD hlinear K) (by
    intro i j h
    have hj : i + 1 = j := h
    subst j
    exact fibreX_comm F ME MD hlinear K i)
private theorem fibreObj_natural {K L : CochainComplex E ℤ} (f : K ⟶ L) :
    (F.mapHomologicalComplex (.up ℤ)).map (ME.fibre.map f) ≫
        (fibreObj F ME MD hlinear L).hom =
      (fibreObj F ME MD hlinear K).hom ≫
        MD.fibre.map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  apply HomologicalComplex.hom_ext
  intro q
  change F.map ((ME.fibre.map f).f q) ≫ (fibreX F ME MD hlinear L q).hom =
    (fibreX F ME MD hlinear K q).hom ≫ _
  apply (cancel_mono (MD.fibreCoordinates _ q).hom).mp
  apply biprod.hom_ext
  · simp only [Category.assoc]
    rw [fibreX_fst, ← F.map_comp_assoc, fibre_map_fst, fibre_map_fst, fibreX_fst_assoc]
    have hh := congrArg (fun t ↦ t.f q) (betaObj_natural F ME MD hlinear f)
    change F.map ((ME.product.map f).f q) ≫ (betaObj F ME MD hlinear L).hom.f q =
      (betaObj F ME MD hlinear K).hom.f q ≫
        (MD.product.map ((F.mapHomologicalComplex (.up ℤ)).map f)).f q at hh
    simp only [Functor.map_comp, Category.assoc, hh]
  · simp only [Category.assoc]
    rw [fibreX_snd, ← F.map_comp_assoc, fibre_map_snd, fibre_map_snd, fibreX_snd_assoc]
    have hh := congrArg (fun t ↦ t.f (q - 1)) (betaObj_natural F ME MD hlinear f)
    change F.map ((ME.product.map f).f (q - 1)) ≫
        (betaObj F ME MD hlinear L).hom.f (q - 1) =
      (betaObj F ME MD hlinear K).hom.f (q - 1) ≫
        (MD.product.map ((F.mapHomologicalComplex (.up ℤ)).map f)).f (q - 1) at hh
    simp only [Functor.map_comp, Category.assoc, hh]
private def fibreComparison : ME.fibre ⋙ F.mapHomologicalComplex (.up ℤ) ≅
    F.mapHomologicalComplex (.up ℤ) ⋙ MD.fibre :=
  NatIso.ofComponents (fibreObj F ME MD hlinear)
    (fun f ↦ fibreObj_natural F ME MD hlinear f)
omit [HasCountableProducts E] in
@[reassoc] private theorem unit_fst (K : CochainComplex E ℤ) (q : ℤ) :
    (ME.unit.app K).f q ≫ (ME.fibreCoordinates K q).hom ≫ biprod.fst =
      (ME.diagonal.app K).f q := by
  rw [← Category.assoc, ME.unit_coordinates]
  exact biprod.lift_fst _ _
omit [HasCountableProducts E] in
@[reassoc] private theorem unit_snd (K : CochainComplex E ℤ) (q : ℤ) :
    (ME.unit.app K).f q ≫ (ME.fibreCoordinates K q).hom ≫ biprod.snd = 0 := by
  rw [← Category.assoc, ME.unit_coordinates]
  exact biprod.lift_snd _ _
private theorem fibreComparison_unit (K : CochainComplex E ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).map (ME.unit.app K) ≫
        (fibreComparison F ME MD hlinear).hom.app K =
      MD.unit.app ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  apply HomologicalComplex.hom_ext
  intro q
  change F.map ((ME.unit.app K).f q) ≫ (fibreX F ME MD hlinear K q).hom = _
  apply (cancel_mono (MD.fibreCoordinates _ q).hom).mp
  apply biprod.hom_ext
  · simp only [Category.assoc]
    rw [fibreX_fst, ← F.map_comp_assoc, unit_fst, unit_fst]
    have hh := congrArg (fun t ↦ t.f q) (beta_diagonal F ME MD hlinear K)
    exact hh
  · simp only [Category.assoc]
    rw [fibreX_snd, ← F.map_comp_assoc, unit_snd, unit_snd]
    simp only [Functor.map_zero, zero_comp]

private def modelsIso (MF : SignedKoszulCompletionModel A E σE a TE) :
    ME.fibre ≅ MF.fibre :=
  (Functor.rightUnitor ME.fibre).symm ≪≫
    Functor.isoWhiskerLeft ME.fibre (Functor.mapHomologicalComplexIdIso E (.up ℤ)).symm ≪≫
    fibreComparison (𝟭 E) ME MF (fun _ _ ↦ rfl) ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso E (.up ℤ)) MF.fibre ≪≫
    Functor.leftUnitor MF.fibre
private theorem countableProducts {A B : Type*} [Category* A] [Category* B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) (h : ∀ M : ℕ → A, IsIso (piComparison F M)) :
    PreservesLimitsOfShape (Discrete ℕ) F where
  preservesLimit {K} := by
    have := h (fun n ↦ K.obj ⟨n⟩)
    have : PreservesLimit (Discrete.functor (K.obj ∘ Discrete.mk)) F :=
      PreservesProduct.of_iso_comparison F (K.obj ∘ Discrete.mk)
    exact preservesLimit_of_iso_diagram F Discrete.natIsoFunctor.symm

end ChainComparison

section DerivedComparison

variable {E : Type cu} [Category.{cv} E] [Abelian E] [HasDerivedCategory.{cw} E]
  {D : Type du} [Category.{dv} D] [Abelian D] [HasDerivedCategory.{dw} D]
private theorem descendUnit
    (H : CochainComplex E ℤ ⥤ CochainComplex E ℤ)
    (hH : (HomologicalComplex.quasiIso E (.up ℤ)).IsInvertedBy (H ⋙ DerivedCategory.Q))
    (η : 𝟭 (CochainComplex E ℤ) ⟶ H) :
    ∃ (HD : DerivedCategory E ⥤ DerivedCategory E)
      (e : DerivedCategory.Q ⋙ HD ≅ H ⋙ DerivedCategory.Q)
      (ηD : 𝟭 (DerivedCategory E) ⟶ HD),
      ∀ K : CochainComplex E ℤ,
        ηD.app (DerivedCategory.Q.obj K) ≫ e.hom.app K =
          DerivedCategory.Q.map (η.app K) := by
  let Q : CochainComplex E ℤ ⥤ DerivedCategory E := DerivedCategory.Q
  let W := HomologicalComplex.quasiIso E (.up ℤ)
  let HD := Localization.lift (H ⋙ Q) hH Q
  let e : Q ⋙ HD ≅ H ⋙ Q := Localization.fac (H ⋙ Q) hH Q
  let ηD : 𝟭 (DerivedCategory E) ⟶ HD :=
    Localization.liftNatTrans Q W Q (H ⋙ Q) (𝟭 _) HD
      ((Functor.leftUnitor Q).inv ≫ Functor.whiskerRight η Q)
  refine ⟨HD, e, ηD, ?_⟩
  intro K
  change (Localization.liftNatTrans Q W Q (H ⋙ Q) (𝟭 _) HD
    ((Functor.leftUnitor Q).inv ≫ Functor.whiskerRight η Q)).app (Q.obj K) ≫
      e.hom.app K = Q.map (η.app K)
  rw [Localization.liftNatTrans_app]
  change (𝟙 _ ≫ (𝟙 _ ≫ Q.map (η.app K)) ≫ e.inv.app K) ≫ e.hom.app K = _
  simp only [Functor.comp_obj, Category.id_comp, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]

private theorem descendComparison
    (F : E ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (H : CochainComplex E ℤ ⥤ CochainComplex E ℤ)
    (G : CochainComplex D ℤ ⥤ CochainComplex D ℤ)
    (hH : (HomologicalComplex.quasiIso E (.up ℤ)).IsInvertedBy (H ⋙ DerivedCategory.Q))
    (hG : (HomologicalComplex.quasiIso D (.up ℤ)).IsInvertedBy (G ⋙ DerivedCategory.Q))
    (η : 𝟭 (CochainComplex E ℤ) ⟶ H) (ε : 𝟭 (CochainComplex D ℤ) ⟶ G)
    (h : H ⋙ F.mapHomologicalComplex (.up ℤ) ≅ F.mapHomologicalComplex (.up ℤ) ⋙ G)
    (hunit : ∀ K : CochainComplex E ℤ,
      (F.mapHomologicalComplex (.up ℤ)).map (η.app K) ≫ h.hom.app K =
        ε.app ((F.mapHomologicalComplex (.up ℤ)).obj K)) :
    ∃ (HD : DerivedCategory E ⥤ DerivedCategory E)
      (GD : DerivedCategory D ⥤ DerivedCategory D)
      (eH : DerivedCategory.Q ⋙ HD ≅ H ⋙ DerivedCategory.Q)
      (eG : DerivedCategory.Q ⋙ GD ≅ G ⋙ DerivedCategory.Q)
      (ηD : 𝟭 (DerivedCategory E) ⟶ HD) (εD : 𝟭 (DerivedCategory D) ⟶ GD)
      (hD : HD ⋙ F.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ GD),
      (∀ K, ηD.app (DerivedCategory.Q.obj K) ≫ eH.hom.app K =
        DerivedCategory.Q.map (η.app K)) ∧
      (∀ K, εD.app (DerivedCategory.Q.obj K) ≫ eG.hom.app K =
        DerivedCategory.Q.map (ε.app K)) ∧
      (∀ K, F.mapDerivedCategory.map (eH.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app (H.obj K) ≫ DerivedCategory.Q.map (h.hom.app K) =
        hD.hom.app (DerivedCategory.Q.obj K) ≫
          GD.map (F.mapDerivedCategoryFactors.hom.app K) ≫
            eG.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K)) ∧
      (∀ X, F.mapDerivedCategory.map (ηD.app X) ≫ hD.hom.app X =
        εD.app (F.mapDerivedCategory.obj X)) := by
  obtain ⟨HD, eH, ηD, hη⟩ := descendUnit H hH η
  obtain ⟨GD, eG, εD, hε⟩ := descendUnit G hG ε
  let Q : CochainComplex E ℤ ⥤ DerivedCategory E := DerivedCategory.Q
  let Q' : CochainComplex D ℤ ⥤ DerivedCategory D := DerivedCategory.Q
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let FD := F.mapDerivedCategory
  let e : Q ⋙ (HD ⋙ FD) ≅ Q ⋙ (FD ⋙ GD) :=
    (Functor.associator Q HD FD).symm ≪≫ Functor.isoWhiskerRight eH FD ≪≫
      Functor.associator H Q FD ≪≫ Functor.isoWhiskerLeft H F.mapDerivedCategoryFactors ≪≫
      (Functor.associator H Fc Q').symm ≪≫ Functor.isoWhiskerRight h Q' ≪≫
      Functor.associator Fc G Q' ≪≫ Functor.isoWhiskerLeft Fc eG.symm ≪≫
      (Functor.associator Fc Q' GD).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors.symm GD ≪≫ Functor.associator Q FD GD
  let ff := Localization.fullyFaithfulWhiskeringLeft Q
    (HomologicalComplex.quasiIso E (.up ℤ)) (DerivedCategory D)
  let hD : HD ⋙ FD ≅ FD ⋙ GD := ff.preimageIso e
  have he (K : CochainComplex E ℤ) :
      hD.hom.app (Q.obj K) = FD.map (eH.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app (H.obj K) ≫ Q'.map (h.hom.app K) ≫
          eG.inv.app (Fc.obj K) ≫ GD.map (F.mapDerivedCategoryFactors.inv.app K) := by
    have hh := congr_app (ff.map_preimage e.hom) K
    change hD.hom.app (Q.obj K) = e.hom.app K at hh
    simp only [e, Iso.trans_hom, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom] at hh
    dsimp only [Q, Q', Fc, FD, Functor.comp_obj] at hh ⊢
    simpa only [Category.assoc, Category.comp_id, Category.id_comp] using hh
  have hf (K : CochainComplex E ℤ) :
      FD.map (eH.hom.app K) ≫ F.mapDerivedCategoryFactors.hom.app (H.obj K) ≫
        Q'.map (h.hom.app K) =
      hD.hom.app (Q.obj K) ≫ GD.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        eG.hom.app (Fc.obj K) := by
    rw [he]
    dsimp only [Q, Q', Fc, FD, Functor.comp_obj]
    simp only [Functor.comp_obj, Category.assoc, ← GD.map_comp_assoc, Iso.inv_hom_id_app, GD.map_id,
      Category.id_comp, Category.comp_id]
  have hu (K : CochainComplex E ℤ) :
      FD.map (ηD.app (Q.obj K)) ≫ hD.hom.app (Q.obj K) = εD.app (FD.obj (Q.obj K)) := by
    apply (cancel_mono (GD.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      eG.hom.app (Fc.obj K))).mp
    simp only [Category.assoc]
    rw [← hf, ← Category.assoc, ← FD.map_comp, hη]
    rw [F.mapDerivedCategoryFactors_hom_naturality_assoc]
    rw [← Q'.map_comp, hunit]
    rw [← hε]
    have hn := εD.naturality (F.mapDerivedCategoryFactors.hom.app K)
    simpa only [Functor.id_map, Functor.id_obj, Functor.comp_obj, Category.assoc] using
      congrArg (fun t ↦ t ≫ eG.hom.app (Fc.obj K)) hn
  have hall :
      (Functor.leftUnitor FD).inv ≫ Functor.whiskerRight ηD FD ≫ hD.hom =
        (Functor.rightUnitor FD).inv ≫ Functor.whiskerLeft FD εD := by
    apply Localization.natTrans_ext Q (HomologicalComplex.quasiIso E (.up ℤ))
    intro K
    simpa using hu K
  refine ⟨HD, GD, eH, eG, ηD, εD, hD, hη, hε, hf, ?_⟩
  intro X
  simpa using congr_app hall X

end DerivedComparison

end

end SignedKoszulComparisonAux

/-- Exact A-linear functors preserving the canonical countable products commute with the
explicit signed Koszul fibre and its coaugmentation, on complexes and after localization.
The finite-coordinate, product-projection and two fibre-projection equations specify the
canonical comparison. Both model types are inhabited, and the comparison applies to every
model with these specified coordinates. Exponent m+1 indexes exactly all positive exponents.

Source: Stacks Tag 0A0E and the agent-written refinement of the blueprint proof
lem-cbc-completed-extension-zero-comparison (blueprint: lem-cbc-exact-linear-koszul-fiber).

Proof plan:
1. Expand the ordered total tensor into summands K^(q+|I|). The pure-tensor unitors give
   the normalization in the model. The differential has entries d_K and
   (-1)^(q+|I|) (-1)^(number of earlier indices) a_i^(m+1). The transition on I is
   multiplication by the product of its scalars. This also constructs both models.
2. Additivity preserves finite biproduct inclusions and projections, because their matrix
   composites and the sum of inclusion-projection composites are preserved. A-linearity
   preserves each scalar differential and transition entry. This gives alpha, natural in K,
   compatible with transitions and with the empty-coordinate inclusions.
3. Compose the assumed canonical countable-product comparison with the product of alpha.
   Projection to m gives the equation for beta below; projection also proves its chain
   equation, naturality, and compatibility with the shift and the diagonal unit.
4. The binary-biproduct comparison followed by beta in degrees q and q-1 gives h. Its
   block differential is (d,0;1-s,-d), so it is a chain isomorphism. Its unit equality follows
   in the first coordinate from the empty-subset inclusions, and in the second from F(0)=0.
5. By lem-sbc-koszul-fibre-linear-descent, exact countable products and the bounded finite
   free Koszul factors imply that both signed models preserve quasi-isomorphisms on all
   unbounded complexes. Exact F descends termwise by
   lem-sf-exact-functor-derived-triangulated, using F.mapDerivedCategory.
6. Localize h and the unit equality by lem-weil-pbc-localization-universal-property.
   The displayed factorization equation identifies the derived comparison with the same
   chain comparison. The inverse of the final unit is the inverse comparison followed by the
   image of the
   inverse source unit. For r=0 there is just the empty coordinate,
   all transitions are identities, and the same product-diagonal argument applies. No
   scalar is inverted, so zero scalars, units, zero objects and the empty site are allowed. -/
theorem exists_exactLinear_signedKoszulFibre
    {C : Type u} [SmallCategory C] {D : Type v} [SmallCategory D]
    {J : GrothendieckTopology C} {L : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf L CommRingCat.{v})
    {A : Type z} [CommRing A]
    (ρR : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat))
    (ρS : A →+* RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
    [HasDerivedCategory.{wR} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{v}
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))]
    [HasCountableProducts (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasCountableProducts (ringedSiteModules.{v}
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))]
    [CountableAB4Star (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [CountableAB4Star (ringedSiteModules.{v}
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))]
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{v} ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hlinear : ∀ {M N : ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} (b : A) (f : M ⟶ N),
      F.map (ringedKoszulCoefficientSMul R ρR b f) =
        ringedKoszulCoefficientSMul S ρS b (F.map f))
    (hproduct : ∀ M : ℕ → ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
      IsIso (piComparison F M))
    (r : ℕ) (a : Fin r → A) :
    Nonempty (RingedSignedKoszulCompletionModel R ρR a) ∧
    Nonempty (RingedSignedKoszulCompletionModel S ρS a) ∧
    ∀ (MR : RingedSignedKoszulCompletionModel R ρR a)
      (MS : RingedSignedKoszulCompletionModel S ρS a),
    Nonempty (ExactLinearSignedKoszulFibreComparison R S ρR ρS F MR MS) := by
  let := Abelian.hasFiniteBiproducts (C := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  let := Abelian.hasFiniteBiproducts (C := ringedSiteModules.{v}
    ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))
  obtain ⟨MR₀, hR₀⟩ := exists_ringedSignedKoszulCompletionModel R ρR r a
  obtain ⟨MS₀, hS₀⟩ := exists_ringedSignedKoszulCompletionModel S ρS r a
  refine ⟨⟨MR₀⟩, ⟨MS₀⟩, ?_⟩
  intro MR MS
  let := SignedKoszulComparisonAux.countableProducts F hproduct
  let h := SignedKoszulComparisonAux.fibreComparison F MR.model MS.model hlinear
  have hR : (HomologicalComplex.quasiIso
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (.up ℤ)).IsInvertedBy (MR.model.fibre ⋙ DerivedCategory.Q) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _
      (Functor.isoWhiskerRight
        (SignedKoszulComparisonAux.modelsIso MR.model MR₀.model) DerivedCategory.Q)).mpr hR₀
  have hS : (HomologicalComplex.quasiIso
      (ringedSiteModules.{v} ((sheafCompose L (forget₂ CommRingCat RingCat)).obj S))
      (.up ℤ)).IsInvertedBy (MS.model.fibre ⋙ DerivedCategory.Q) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _
      (Functor.isoWhiskerRight
        (SignedKoszulComparisonAux.modelsIso MS.model MS₀.model) DerivedCategory.Q)).mpr hS₀
  obtain ⟨HR, HS, eR, eS, etaR, etaS, hd, hηR, hηS, hfac, hunit⟩ :=
    SignedKoszulComparisonAux.descendComparison F MR.model.fibre MS.model.fibre
      hR hS MR.model.unit MS.model.unit h
      (SignedKoszulComparisonAux.fibreComparison_unit F MR.model MS.model hlinear)
  refine ⟨{
    alpha := SignedKoszulComparisonAux.alpha F MR.model MS.model hlinear
    beta := SignedKoszulComparisonAux.beta F MR.model MS.model hlinear
    h := h
    HR := HR
    HS := HS
    eR := eR
    eS := eS
    etaR := etaR
    etaS := etaS
    hd := hd
    alpha_coordinates := SignedKoszulComparisonAux.alpha_coordinates F MR.model MS.model hlinear
    beta_projection := SignedKoszulComparisonAux.beta_projection F MR.model MS.model hlinear
    h_fst := SignedKoszulComparisonAux.fibreX_fst F MR.model MS.model hlinear
    h_snd := SignedKoszulComparisonAux.fibreX_snd F MR.model MS.model hlinear
    unit_compatibility :=
      SignedKoszulComparisonAux.fibreComparison_unit F MR.model MS.model hlinear
    etaR_factor := hηR
    etaS_factor := hηS
    derived_factor := hfac
    derived_unit := hunit
    preserves_unit_isIso := ?_ }⟩
  intro X hx
  let := hx
  have hi : IsIso (F.mapDerivedCategory.map (etaR.app X) ≫ hd.hom.app X) := inferInstance
  rwa [hunit] at hi

end CategoryTheory
