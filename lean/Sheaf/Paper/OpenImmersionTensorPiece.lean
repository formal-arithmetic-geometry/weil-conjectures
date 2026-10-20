/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
public import Sheaf.Paper.StrictPerfectPackageOnSite
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.Paper.RingedProjectionRestriction
public import Sheaf.Paper.ProjectionCompactification
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# The open-immersion piece of the projection formula

Source: Weil conjectures blueprint, proper base change, lemma 1269;
Stacks Project, Tags 03DI, 03DJ, 03EL, 06YQ and 07A4
(blueprint: lemma-weil-pbc-projection-formula-open-piece).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction

namespace SheafOfModules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MonoidalCategory

-- The ordinary slice formula gives closure of the image of extension under tensor.
-- For a subterminal slice object the adjunction unit is invertible, so the general
-- adjunction projection-map criterion identifies the normalized derived comparison.

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C}

universe u₀ v₀ r

private theorem monoidal_comparison_naturality
    {D E : Type*} [Category* D] [Category* E]
    [MonoidalCategory D] [MonoidalCategory E]
    (S : D ⥤ E) [S.LaxMonoidal]
    {A B X Y : E} {A' B' X' Y' : D}
    (f : A ⟶ B) (g : X ⟶ Y) (a : A' ⟶ B') (b : X' ⟶ Y')
    (eA : A ⟶ S.obj A') (eB : B ⟶ S.obj B')
    (eX : X ⟶ S.obj X') (eY : Y ⟶ S.obj Y')
    (hf : f ≫ eB = eA ≫ S.map a) (hg : g ≫ eY = eX ≫ S.map b) :
    (f ⊗ₘ g) ≫ ((eB ⊗ₘ eY) ≫ Functor.LaxMonoidal.μ S B' Y') =
      ((eA ⊗ₘ eX) ≫ Functor.LaxMonoidal.μ S A' X') ≫ S.map (a ⊗ₘ b) := by
  rw [← Category.assoc, tensorHom_comp_tensorHom, hf, hg,
    ← tensorHom_comp_tensorHom, Category.assoc, Functor.LaxMonoidal.μ_natural,
    Category.assoc]

private theorem monoidal_tensor_presentation
    {D E : Type*} [Category* D] [Category* E]
    [MonoidalCategory D] [MonoidalCategory E]
    (F : E ⥤ D) (S : D ⥤ E) [S.Monoidal] (c : F ⋙ S ≅ 𝟭 E) :
    Nonempty (MonoidalCategory.tensor E ≅
      (F.prod F) ⋙ MonoidalCategory.tensor D ⋙ S) := by
  refine ⟨NatIso.ofComponents
    (fun X ↦ tensorIso (c.symm.app X.1) (c.symm.app X.2) ≪≫
      Functor.Monoidal.μIso S (F.obj X.1) (F.obj X.2)) ?_⟩
  intro X Y f
  dsimp only [Iso.trans_hom, tensorIso_hom, Iso.app_hom, Iso.symm_hom,
    Functor.Monoidal.μIso_hom,
    Functor.comp_map, Functor.prod_map, MonoidalCategory.tensor_map]
  exact monoidal_comparison_naturality S f.1 f.2 (F.map f.1) (F.map f.2)
    (c.inv.app X.1) (c.inv.app Y.1) (c.inv.app X.2) (c.inv.app Y.2)
    (c.inv.naturality f.1) (c.inv.naturality f.2)

private theorem restrictScalars_identity
    {D : Type*} [Category* D] (R : Dᵒᵖ ⥤ RingCat.{r}) :
    PresheafOfModules.restrictScalars.{r} (𝟙 R) = 𝟭 _ := by
  rfl

private theorem sheaf_tensor_presentation
    {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    (R : Sheaf J CommRingCat.{r})
    [(J.W.inverseImage (PresheafOfModules.toPresheaf.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)).IsMonoidal] :
    let := monoidalCategory R
    let A := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
    Nonempty (MonoidalCategory.tensor (SheafOfModules.{r} A) ≅
      ((forget.{r} A).prod (forget.{r} A)) ⋙
        MonoidalCategory.tensor (PresheafOfModules.{r} A.obj) ⋙
          PresheafOfModules.sheafification (𝟙 A.obj)) := by
  let := monoidalCategory R
  let A := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
  let F := forget.{r} A
  let S := PresheafOfModules.sheafification.{r} (R := A) (𝟙 A.obj)
  let c : F ⋙ S ≅ 𝟭 _ := by
    have e := asIso
      (PresheafOfModules.sheafificationAdjunction.{r} (R := A) (𝟙 A.obj)).counit
    simpa only [restrictScalars_identity, Functor.comp_id] using e
  exact monoidal_tensor_presentation F S c

private theorem naturality_comp {D : Type*} [Category* D]
    {A B C A' B' C' : D} {f : A ⟶ A'} {g : B ⟶ B'} {h : C ⟶ C'}
    {s : A ⟶ B} {s' : A' ⟶ B'} {t : B ⟶ C} {t' : B' ⟶ C'}
    (hs : f ≫ s' = s ≫ g) (ht : g ≫ t' = t ≫ h) :
    f ≫ (s' ≫ t') = (s ≫ t) ≫ h := by
  rw [← Category.assoc, hs, Category.assoc, ht, Category.assoc]

private theorem naturality_inv {D : Type*} [Category* D]
    {A B A' B' : D} (i : A ≅ B) (j : A' ≅ B')
    {f : A ⟶ A'} {g : B ⟶ B'} (h : f ≫ j.hom = i.hom ≫ g) :
    g ≫ j.inv = i.inv ≫ f := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

private theorem extension_tensor_of_presentations
    {D E D' E' : Type*} [Category* D] [Category* E] [Category* D'] [Category* E']
    [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory D'] [MonoidalCategory E']
    (L : D ⥤ E) (V : E ⥤ D) (F : D ⥤ D') (G : E ⥤ E')
    (S : D' ⥤ D) (T : E' ⥤ E)
    (p : MonoidalCategory.tensor D ≅ (F.prod F) ⋙ MonoidalCategory.tensor D' ⋙ S)
    (q : MonoidalCategory.tensor E ≅ (G.prod G) ⋙ MonoidalCategory.tensor E' ⋙ T)
    (e : (F.prod (V ⋙ F)) ⋙ MonoidalCategory.tensor D' ⋙ S ⋙ L ≅
      ((L ⋙ G).prod G) ⋙ MonoidalCategory.tensor E' ⋙ T) :
    ∃ d : ∀ (X : D) (Y : E), L.obj (X ⊗ V.obj Y) ≅ L.obj X ⊗ Y,
      ∀ (X X' : D) (Y Y' : E) (a : X ⟶ X') (b : Y ⟶ Y'),
        L.map (a ⊗ₘ V.map b) ≫ (d X' Y').hom =
          (d X Y).hom ≫ (L.map a ⊗ₘ b) := by
  refine ⟨fun X Y ↦ L.mapIso (p.app (X, V.obj Y)) ≪≫ e.app (X, Y) ≪≫
    (q.app (L.obj X, Y)).symm, ?_⟩
  intro X X' Y Y' a b
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  have h₁ := congrArg L.map (p.hom.naturality
    (X := (X, V.obj Y)) (Y := (X', V.obj Y')) (a, V.map b))
  have h₂ := e.hom.naturality (X := (X, Y)) (Y := (X', Y')) (a, b)
  have h₃ := q.hom.naturality
    (X := (L.obj X, Y)) (Y := (L.obj X', Y')) (L.map a, b)
  simp only [Functor.map_comp, Functor.comp_map, Functor.prod_map,
    MonoidalCategory.tensor_map] at h₁ h₂ h₃
  exact naturality_comp h₁ (naturality_comp h₂
    (naturality_inv (q.app (L.obj X, Y)) (q.app (L.obj X', Y')) h₃))

set_option backward.isDefEq.respectTransparency false in
private theorem extension_tensor_natural
    {C : Type u₀} [Category.{v₀} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max u₀ v₀ r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u₀ v₀ r}]
    (R : Sheaf J CommRingCat.{max u₀ v₀ r}) (U : C) :
    let := isMonoidal_W_independentCoefficients R
    let : HasSheafify (J.over U) AddCommGrpCat.{max u₀ v₀ r} :=
      hasSheafify_coefficientUniverse.{max u₀ v₀, v₀, max u₀ v₀ r} (J := J.over U)
    let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u₀ v₀ r} :=
      wEqualsLocallyBijective_coefficientUniverse.{max u₀ v₀, v₀, max u₀ v₀ r} (J := J.over U)
    let := isMonoidal_W_independentCoefficients (R.over U)
    let := monoidalCategory R
    let : MonoidalCategory (SheafOfModules.{max u₀ v₀ r}
      (((sheafCompose J
        (forget₂ CommRingCat.{max u₀ v₀ r} RingCat.{max u₀ v₀ r})).obj R).over U)) :=
      monoidalCategory (R.over U)
    let A := (sheafCompose J
      (forget₂ CommRingCat.{max u₀ v₀ r} RingCat.{max u₀ v₀ r})).obj R
    let L := extensionByZeroPresheaf.{max u₀ v₀ r} A U ⋙
      PresheafOfModules.sheafification (𝟙 A.obj)
    let V := overFunctor.{max u₀ v₀ r} A U
    ∃ e : ∀ (G : SheafOfModules.{max u₀ v₀ r} (A.over U))
      (F : SheafOfModules.{max u₀ v₀ r} A), L.obj (G ⊗ V.obj F) ≅ L.obj G ⊗ F,
      ∀ (G H : SheafOfModules.{max u₀ v₀ r} (A.over U))
        (F E : SheafOfModules.{max u₀ v₀ r} A) (a : G ⟶ H) (b : F ⟶ E),
        L.map (a ⊗ₘ V.map b) ≫ (e H E).hom =
          (e G F).hom ≫ (L.map a ⊗ₘ b) := by
  let := isMonoidal_W_independentCoefficients R
  let : HasSheafify (J.over U) AddCommGrpCat.{max u₀ v₀ r} :=
    hasSheafify_coefficientUniverse.{max u₀ v₀, v₀, max u₀ v₀ r} (J := J.over U)
  let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u₀ v₀ r} :=
    wEqualsLocallyBijective_coefficientUniverse.{max u₀ v₀, v₀, max u₀ v₀ r} (J := J.over U)
  let := isMonoidal_W_independentCoefficients (R.over U)
  let := monoidalCategory R
  let := monoidalCategory (R.over U)
  let A := (sheafCompose J
    (forget₂ CommRingCat.{max u₀ v₀ r} RingCat.{max u₀ v₀ r})).obj R
  let : MonoidalCategory (SheafOfModules.{max u₀ v₀ r} (A.over U)) :=
    monoidalCategory (R.over U)
  let L := extensionByZeroPresheaf.{max u₀ v₀ r} A U ⋙
      PresheafOfModules.sheafification (𝟙 A.obj)
  let V := overFunctor.{max u₀ v₀ r} A U
  let : MonoidalCategory (PresheafOfModules.{max u₀ v₀ r} (A.over U).obj) := by
    change MonoidalCategory (PresheafOfModules.{max u₀ v₀ r}
      ((R.over U).obj ⋙ forget₂ CommRingCat RingCat))
    exact PresheafOfModules.monoidalCategory
  let : MonoidalCategory (PresheafOfModules.{max u₀ v₀ r} A.obj) := by
    change MonoidalCategory (PresheafOfModules.{max u₀ v₀ r}
      (R.obj ⋙ forget₂ CommRingCat RingCat))
    exact PresheafOfModules.monoidalCategory
  obtain ⟨sU⟩ := sheaf_tensor_presentation (R.over U)
  obtain ⟨sR⟩ := sheaf_tensor_presentation R
  obtain ⟨e⟩ := ringedSlice_extension_tensor.{u₀, max u₀ v₀ r, v₀} J R U
  exact extension_tensor_of_presentations L V (forget (A.over U)) (forget A)
    (PresheafOfModules.sheafification (𝟙 (A.over U).obj))
    (PresheafOfModules.sheafification (𝟙 A.obj)) sU sR e

attribute [local irreducible] SheafOfModules.monoidalCategory

set_option backward.isDefEq.respectTransparency false in
private theorem total_extension_iso
    {D E : Type*} [Category* D] [Category* E] [Abelian D] [Abelian E]
    [MonoidalCategory D] [MonoidalCategory E]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ X : D, ((curriedTensor D).obj X).PreservesZeroMorphisms]
    [(curriedTensor E).PreservesZeroMorphisms]
    [∀ X : E, ((curriedTensor E).obj X).PreservesZeroMorphisms]
    [HasCoproducts.{0} D] [HasCoproducts.{0} E]
    (L : D ⥤ E) (V : E ⥤ D) [L.Additive] [V.PreservesZeroMorphisms]
    [PreservesColimitsOfSize.{0, 0} L]
    (e : ∀ G : D, ∀ F : E, L.obj (G ⊗ V.obj F) ≅ L.obj G ⊗ F)
    (he : ∀ (G H : D) (F E : E) (a : G ⟶ H) (b : F ⟶ E),
      L.map (a ⊗ₘ V.map b) ≫ (e H E).hom = (e G F).hom ≫ (L.map a ⊗ₘ b))
    (G : CochainComplex D ℤ) (K : CochainComplex E ℤ) :
    Nonempty (((L.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor G ((V.mapHomologicalComplex (.up ℤ)).obj K)
        (curriedTensor D))) ≅
      CochainComplex.mapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj G) K
        (curriedTensor E)) := by
  classical
  let LC := L.mapHomologicalComplex (.up ℤ)
  let VC := V.mapHomologicalComplex (.up ℤ)
  let T := (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj G).obj
    (VC.obj K)
  have : L.PreservesTotalComplex T (.up ℤ) := fun _ ↦ inferInstance
  let t := (HomologicalComplex₂.mapTotalIso L T (.up ℤ)).symm
  let f :
      (((L.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj T) ≅
      (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
        (LC.obj G)).obj K :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ e (G.X p) (K.X q)) (by
          intro q q' hq
          change (e (G.X p) (K.X q)).hom ≫
            whiskerLeft (L.obj (G.X p)) (K.d q q') =
            L.map (whiskerLeft (G.X p) (V.map (K.d q q'))) ≫
              (e (G.X p) (K.X q')).hom
          have hh := he (G.X p) (G.X p) (K.X q) (K.X q') (𝟙 _) (K.d q q')
          rw [L.map_id, id_tensorHom, id_tensorHom] at hh
          exact hh.symm))
      (by
        intro p p' hp
        apply HomologicalComplex.Hom.ext
        funext q
        change (e (G.X p) (K.X q)).hom ≫
            whiskerRight (L.map (G.d p p')) (K.X q) =
          L.map (whiskerRight (G.d p p') (V.obj (K.X q))) ≫
            (e (G.X p') (K.X q)).hom
        have hh := he (G.X p) (G.X p') (K.X q) (K.X q) (G.d p p') (𝟙 _)
        rw [V.map_id, tensorHom_id, tensorHom_id] at hh
        exact hh.symm)
  exact ⟨t ≪≫ HomologicalComplex₂.total.mapIso f (.up ℤ)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_right_quasiIso
    {D : Type*} [Category* D] [Abelian D] [MonoidalCategory D]
    [MonoidalPreadditive D] [HasCoproducts.{0} D]
    {E E' K : CochainComplex D ℤ} (α : E ⟶ E') (hα : QuasiIso α)
    (hK : ∀ A : CochainComplex D ℤ, A.Acyclic →
      (CochainComplex.mapBifunctor A K (curriedTensor D)).Acyclic) :
    QuasiIso (HomologicalComplex.mapBifunctorMap α (𝟙 K)
      (MonoidalCategory.curriedTensor _) (.up ℤ)) := by
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (CochainComplex.mappingCone α) hc
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht i).of_iso
    (CochainComplex.mapBifunctorMappingCone₁Iso α K (MonoidalCategory.curriedTensor _))

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_left_quasiIso
    {D : Type*} [Category* D] [Abelian D] [MonoidalCategory D]
    [MonoidalPreadditive D] [HasCoproducts.{0} D] [BraidedCategory D]
    {K E E' : CochainComplex D ℤ} (α : E ⟶ E') (hα : QuasiIso α)
    (hK : ∀ A : CochainComplex D ℤ, A.Acyclic →
      (CochainComplex.mapBifunctor A K (curriedTensor D)).Acyclic) :
    QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 K) α
      (MonoidalCategory.curriedTensor _) (.up ℤ)) := by
  have hc := (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (CochainComplex.mappingCone α) hc
  let F := MonoidalCategory.curriedTensor D
  let e : (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj K) ≅
      (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (CochainComplex.mappingCone α)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ β_ ((CochainComplex.mappingCone α).X p) (K.X q)) (by
          intro q q' hqq'
          exact (BraidedCategory.braiding_naturality_right
            ((CochainComplex.mappingCone α).X p) (K.d q q')).symm)) (by
        intro p p' hpp'
        ext q : 1
        exact (BraidedCategory.braiding_naturality_left
          ((CochainComplex.mappingCone α).d p p') (K.X q)).symm)
  have ht' : (CochainComplex.mapBifunctor K (CochainComplex.mappingCone α) F).Acyclic := by
    intro i
    exact (ht i).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
      HomologicalComplex.mapBifunctorFlipIso K (CochainComplex.mappingCone α) F (.up ℤ))
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht' i).of_iso (CochainComplex.mapBifunctorMappingCone₂Iso K α F)

set_option backward.isDefEq.respectTransparency false in
private theorem tensorModel_oneFlat (R : Sheaf J CommRingCat.{u + 1})
    (a : TensorModel R) (P Q : CochainComplex (Mod R) ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q) :
    Nonempty (a.functor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≅
      DerivedCategory.Q.obj ((total R).obj (P, Q))) := by
  let : HasDerivedCategory (Mod R) :=
    AlgebraicGeometry.Scheme.ProjectionRestriction.derived R
  classical
  let := monoidalCategory R
  let := symmetricCategory R
  let := a.preadditive
  obtain ⟨P₀, f, hP₀, flatP₀, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
  obtain ⟨Q₀, g, hQ₀, flatQ₀, hg, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) Q
  have hp : resolving R P₀ := by
    refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P₀).1 hP₀, ?_⟩
    intro n
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P₀.X n)).symm
      (flatP₀ n)
  have hq : resolving R Q₀ := by
    refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q₀).1 hQ₀, ?_⟩
    intro n
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (Q₀.X n)).symm
      (flatQ₀ n)
  let eP := Localization.isoOfHom DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) f hf
  let eQ := Localization.isoOfHom DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) g hg
  let eg := Localization.isoOfHom DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
    (HomologicalComplex.mapBifunctorMap (𝟙 P₀) g (tensor R) (.up ℤ))
    (tensor_left_quasiIso g hg hP₀)
  let ef := Localization.isoOfHom DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
    (HomologicalComplex.mapBifunctorMap f (𝟙 Q) (tensor R) (.up ℤ))
    (tensor_right_quasiIso f hf hQ)
  exact ⟨a.functor.mapIso (Iso.prod eP.symm eQ.symm) ≪≫
    a.representative.symm.app (⟨P₀, hp⟩, ⟨Q₀, hq⟩) ≪≫ eg ≪≫ ef⟩

set_option backward.isDefEq.respectTransparency false in
private theorem extension_tensor_image (R : Sheaf J CommRingCat.{u + 1}) (U : C)
    (P : CochainComplex (Mod (R.over U)) ℤ) (K : CochainComplex (Mod R) ℤ) :
    ∃ Z : Der (R.over U), Nonempty
      (DerivedCategory.Q.obj ((total R).obj
        (((localizedModuleExtension R U).mapHomologicalComplex (.up ℤ)).obj P, K)) ≅
          (localizedModuleExtension R U).mapDerivedCategory.obj Z) := by
  let : HasDerivedCategory (Mod R) :=
    AlgebraicGeometry.Scheme.ProjectionRestriction.derived R
  let : HasDerivedCategory (Mod (R.over U)) :=
    AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOver R U
  classical
  let := monoidalCategory R
  let := monoidalCategory (R.over U)
  let : MonoidalCategory (SheafOfModules.{u + 1}
      (((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U)) :=
    monoidalCategory (R.over U)
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let D := SheafOfModules.{u + 1}
    (((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U)
  have : (curriedTensor D).PreservesZeroMorphisms :=
    preservesZeroMorphisms_curriedTensor_independentCoefficients (R.over U)
  have (M : SheafOfModules.{u + 1}
      (((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U)) :
      ((curriedTensor _).obj M).PreservesZeroMorphisms :=
    preservesZeroMorphisms_curriedTensor_obj_independentCoefficients (R.over U) M
  let L := localizedModuleExtension R U
  let V := localizedModuleRestriction R U
  let LC := L.mapHomologicalComplex (.up ℤ)
  let VC := V.mapHomologicalComplex (.up ℤ)
  have : PreservesColimitsOfSize.{0, 0} L :=
    (localizedModuleAdjunctionIndependent R U).leftAdjoint_preservesColimits
  obtain ⟨e, he⟩ := extension_tensor_natural.{u + 1, u, 0} J R U
  obtain ⟨d⟩ := total_extension_iso L V e he P K
  have : (tensor (R.over U)).PreservesZeroMorphisms :=
    preservesZeroMorphisms_curriedTensor_independentCoefficients (R.over U)
  have (M : Mod (R.over U)) : ((tensor (R.over U)).obj M).PreservesZeroMorphisms :=
    preservesZeroMorphisms_curriedTensor_obj_independentCoefficients (R.over U) M
  let T := CochainComplex.mapBifunctor P (VC.obj K) (tensor (R.over U))
  refine ⟨DerivedCategory.Q.obj T, ⟨?_⟩⟩
  exact DerivedCategory.Q.mapIso d.symm ≪≫ (L.mapDerivedCategoryFactors.app T).symm

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_supported (R : Sheaf J CommRingCat.{u + 1}) (U : C)
    (a : TensorModel R) (E : Der (R.over U)) (F : Der R) :
    ∃ Z : Der (R.over U), Nonempty
      (a.functor.obj ((localizedModuleExtension R U).mapDerivedCategory.obj E, F) ≅
        (localizedModuleExtension R U).mapDerivedCategory.obj Z) := by
  let : HasDerivedCategory (Mod R) :=
    AlgebraicGeometry.Scheme.ProjectionRestriction.derived R
  let : HasDerivedCategory (Mod (R.over U)) :=
    AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOver R U
  classical
  let L := localizedModuleExtension R U
  let P := DerivedCategory.Q.objPreimage E
  obtain ⟨K, f, hK, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := R) (DerivedCategory.Q.objPreimage F)
  let eF : DerivedCategory.Q.obj K ≅ F :=
    Localization.isoOfHom DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ)) f hf ≪≫
      DerivedCategory.Q.objObjPreimageIso F
  obtain ⟨c⟩ := tensorModel_oneFlat R a ((L.mapHomologicalComplex (.up ℤ)).obj P) K hK
  obtain ⟨Z, ⟨d⟩⟩ := extension_tensor_image R U P K
  refine ⟨Z, ⟨?_⟩⟩
  exact a.functor.mapIso (Iso.prod
      (L.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫
        L.mapDerivedCategoryFactors.app P) eF.symm) ≪≫ c ≪≫ d

open Classical in
private theorem extension_restrict_summand
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (U : C)
    (F : SheafOfModules.{u + 1} (R.over U)) {V W : Cᵒᵖ} (a : V ⟶ W)
    (φ : V.unop ⟶ U) (ψ : W.unop ⟶ U) (h : a.unop ≫ φ = ψ)
    (x : F.val.obj (Opposite.op (Over.mk φ))) :
    extensionByZeroPresheafRestrictAdd R U F a
        (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x) =
      DirectSum.of (fun χ : W.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk χ))) ψ
        (F.val.map (Opposite.op (Over.homMk a.unop h : Over.mk ψ ⟶ Over.mk φ)) x) := by
  subst ψ
  change (DirectSum.toAddMonoid _)
    (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x) = _
  rw [DirectSum.toAddMonoid_of]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem open_unit_iso (R : Sheaf J CommRingCat.{u + 1}) (U : C)
    (hU : ∀ V : C, Subsingleton (V ⟶ U)) (M : Mod (R.over U)) :
    IsIso ((localizedModuleAdjunctionIndependent R U).unit.app M) := by
  classical
  let instDec (V : C) : DecidableEq (V ⟶ U) := Classical.decEq _
  let A := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let P := (extensionByZeroPresheaf.{u + 1} A U).obj M
  let F := (Over.forget U).op
  let e : M.val.presheaf ⟶ F ⋙ P.presheaf :=
    { app W := AddCommGrpCat.ofHom
        ((DirectSum.lof (R.obj.obj (Opposite.op W.unop.left)) (W.unop.left ⟶ U)
          (fun φ ↦ M.val.obj (Opposite.op (Over.mk φ))) W.unop.hom).toAddMonoidHom)
      naturality := by
        intro V W f
        ext x
        change DirectSum.of _ W.unop.hom (M.val.map f x) =
          extensionByZeroPresheafRestrictAdd A U M (F.map f)
            (DirectSum.of _ V.unop.hom x)
        have hr : extensionByZeroPresheafRestrictAdd A U M (F.map f)
            (DirectSum.of _ V.unop.hom x) =
            DirectSum.of _ W.unop.hom (M.val.map f x) := by
          have hh := extension_restrict_summand A U M (F.map f)
            V.unop.hom W.unop.hom (Over.w f.unop) x
          have hf : (Over.homMk f.unop.left (Over.w f.unop) : W.unop ⟶ V.unop) =
              f.unop := by ext; rfl
          change extensionByZeroPresheafRestrictAdd A U M (F.map f) _ =
            DirectSum.of _ W.unop.hom
              (M.val.map (Opposite.op
                (Over.homMk f.unop.left (Over.w f.unop) : W.unop ⟶ V.unop)) x) at hh
          rw [hf] at hh
          exact hh
        exact hr.symm }
  have heapp (W : (Over U)ᵒᵖ) : IsIso (e.app W) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    change Function.Bijective
      (DirectSum.lof (R.obj.obj (Opposite.op W.unop.left)) (W.unop.left ⟶ U)
        (fun φ ↦ M.val.obj (Opposite.op (Over.mk φ))) W.unop.hom)
    constructor
    · exact DirectSum.of_injective
        (β := fun φ : W.unop.left ⟶ U ↦ M.val.obj (Opposite.op (Over.mk φ))) W.unop.hom
    · intro x
      induction x using DirectSum.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | of φ x =>
        have : φ = W.unop.hom := (hU _).elim _ _
        subst φ
        exact ⟨x, rfl⟩
      | add x y hx hy =>
        obtain ⟨x, rfl⟩ := hx
        obtain ⟨y, rfl⟩ := hy
        exact ⟨x + y, map_add _ _ _⟩
  have he : IsIso e := NatIso.isIso_of_isIso_app e
  let η := CategoryTheory.toSheafify J P.presheaf
  let ηU := Functor.whiskerLeft F η
  have : Presheaf.IsLocallyInjective (J.over U) ηU :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) η
  have : Presheaf.IsLocallySurjective (J.over U) ηU :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) η
  let f := (toSheaf (A.over U)).map
    ((localizedModuleAdjunctionIndependent R U).unit.app M)
  have hf : f.hom = e ≫ ηU := by
    ext W x
    have hh := (Classical.choose_spec
      (localizedModuleAdjunctionIndependent_existsUnique R U).exists) M W x
    refine hh.trans ?_
    rfl
  have : Presheaf.IsLocallyInjective (J.over U) f.hom := by rw [hf]; infer_instance
  have : Presheaf.IsLocallySurjective (J.over U) f.hom := by rw [hf]; infer_instance
  have : IsIso f := (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨inferInstance, inferInstance⟩
  exact isIso_of_reflects_iso _ (toSheaf (A.over U))

set_option backward.isDefEq.respectTransparency false in
private theorem derived_open_unit_iso (R : Sheaf J CommRingCat.{u + 1}) (U : C)
    (hU : ∀ V : C, Subsingleton (V ⟶ U)) :
    IsIso (localizedModuleDerivedAdjunction R U).unit := by
  let : HasDerivedCategory (Mod R) :=
    AlgebraicGeometry.Scheme.ProjectionRestriction.derived R
  let : HasDerivedCategory (Mod (R.over U)) :=
    AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOver R U
  let L := localizedModuleExtension R U
  let V := localizedModuleRestriction R U
  let : CatCommSq (L.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q L.mapDerivedCategory :=
    ⟨L.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (V.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q V.mapDerivedCategory :=
    ⟨V.mapDerivedCategoryFactors.symm⟩
  have h (P : CochainComplex (Mod (R.over U)) ℤ) :
      IsIso ((localizedModuleDerivedAdjunction R U).unit.app (DerivedCategory.Q.obj P)) := by
    change IsIso ((((localizedModuleAdjunctionIndependent R U).mapHomologicalComplex
      (.up ℤ)).localization DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
        DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
        L.mapDerivedCategory V.mapDerivedCategory).unit.app (DerivedCategory.Q.obj P))
    rw [Adjunction.localization_unit_app]
    have : IsIso (((localizedModuleAdjunctionIndependent R U).mapHomologicalComplex
        (.up ℤ)).unit.app P) := by
      have (n : ℤ) : IsIso ((((localizedModuleAdjunctionIndependent R U).mapHomologicalComplex
          (.up ℤ)).unit.app P).f n) := by
        change IsIso ((localizedModuleAdjunctionIndependent R U).unit.app (P.X n))
        exact open_unit_iso R U hU (P.X n)
      exact HomologicalComplex.Hom.isIso_of_components _
    infer_instance
  have (E : Der (R.over U)) :
      IsIso ((localizedModuleDerivedAdjunction R U).unit.app E) := by
    rw [← NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Q.objObjPreimageIso E)]
    exact h _
  exact NatIso.isIso_of_isIso_app _

/-- The full subcategory on objects admitting a bounded finite-projective representative.
This is a global strict-perfect condition, with degreewise splittings and variable ranks;
it imposes no compatibility of the splittings with the differentials.
Source: blueprint lemma 1269
(blueprint: lemma-weil-pbc-projection-formula-open-piece). -/
def openTensorCoefficients (R : Sheaf J CommRingCat.{u + 1}) : ObjectProperty (Der R) :=
  fun Q ↦ ∃ F : CochainComplex (Mod R) ℤ,
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n)) ∧
      Nonempty (StrictPerfectCoefficientPackageOnSite
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) F) ∧
      Nonempty (Q ≅ DerivedCategory.Q.obj F)

/-- The left side of the open formula, as a bifunctor on unbounded E and strict-perfect F.
Source: blueprint lemma 1269
(blueprint: lemma-weil-pbc-projection-formula-open-piece). -/
def openTensorSource (R : Sheaf J CommRingCat.{u + 1}) (U : C) (a : TensorModel R) :
    Der (R.over U) × (openTensorCoefficients R).FullSubcategory ⥤ Der R :=
  ((localizedModuleExtension R U).mapDerivedCategory.prod (openTensorCoefficients R).ι) ⋙
    a.functor

/-- The right side of the open formula; restriction and extension are computed termwise.
Source: blueprint lemma 1269
(blueprint: lemma-weil-pbc-projection-formula-open-piece). -/
def openTensorTarget (R : Sheaf J CommRingCat.{u + 1}) (U : C)
    (b : TensorModel (R.over U)) :
    Der (R.over U) × (openTensorCoefficients R).FullSubcategory ⥤ Der R :=
  ((𝟭 (Der (R.over U))).prod
    ((openTensorCoefficients R).ι ⋙ (localizedModuleRestriction R U).mapDerivedCategory)) ⋙
      b.functor ⋙ (localizedModuleExtension R U).mapDerivedCategory

/-- The canonical restriction-tensor interface, at fixed original site universes.
Source: Stacks 03EL and 07A4
(blueprint: lemma-weil-pbc-projection-formula-open-piece). -/
abbrev openTensorRestrictionComparison (R : Sheaf J CommRingCat.{u + 1}) (U : C)
    (a : TensorModel R) (b : TensorModel (R.over U)) (r : Restriction R U) :=
  letI : (localizedModuleRestriction R U).Additive :=
    localizedModuleRestriction_additive R U
  TensorComparison (R := R) (S := R.over U)
    (localizedModuleRestriction R U) r.model a b r.ordinaryTensor

/-- The natural open tensor isomorphism with its exact adjunction-unit normalization.
This predicate spells out the canonical map using the existing normalized tensor models.
Source: blueprint lemma 1269; Stacks 03DI and 07A4
(blueprint: lemma-weil-pbc-projection-formula-open-piece). -/
def openTensorFormula (R : Sheaf J CommRingCat.{u + 1}) (U : C)
    (a : TensorModel R) (b : TensorModel (R.over U)) (r : Restriction R U)
    (t : openTensorRestrictionComparison R U a b r) : Prop :=
  letI : (localizedModuleRestriction R U).Additive :=
    localizedModuleRestriction_additive R U
  ∃! beta : openTensorSource R U a ≅ openTensorTarget R U b,
      ∀ (E : Der (R.over U)) (F : (openTensorCoefficients R).FullSubcategory),
        (localizedModuleDerivedAdjunction R U).homEquiv _ _
            (beta.inv.app (E, F)) =
          b.functor.map (CategoryTheory.Prod.mkHom
            ((localizedModuleDerivedAdjunction R U).unit.app E)
            (𝟙 ((localizedModuleRestriction R U).mapDerivedCategory.obj F.obj))) ≫
              t.comparison.inv.app
                ((localizedModuleExtension R U).mapDerivedCategory.obj E, F.obj)

private theorem uncurry_projection_iso
    {D E : Type*} [Category* D] [Category* E]
    (L : D ⥤ E) (V : E ⥤ D) (T : D × D ⥤ D) (T' : E × E ⥤ E)
    (α : (Functor.postcompose₂.obj L).obj
        ((((Functor.whiskeringLeft₂ D).obj (𝟭 D)).obj V).obj (Functor.curry.obj T)) ⟶
      (((Functor.whiskeringLeft₂ E).obj L).obj (𝟭 E)).obj (Functor.curry.obj T'))
    [IsIso α] :
    ∃ β : ((L.prod (𝟭 E)) ⋙ T') ≅ (((𝟭 D).prod V) ⋙ T ⋙ L),
      ∀ (X : D) (Y : E), β.inv.app (X, Y) = (α.app X).app Y := by
  let β : ((L.prod (𝟭 E)) ⋙ T') ≅ (((𝟭 D).prod V) ⋙ T ⋙ L) :=
    NatIso.ofComponents (fun X ↦ (asIso ((α.app X.1).app X.2)).symm) (by
      intro X Y f
      dsimp only [Iso.symm_hom]
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
      have hn := (Functor.uncurry.map α).naturality f
      simpa [← Functor.map_comp] using hn.symm)
  exact ⟨β, fun _ _ ↦ rfl⟩

private theorem uncurried_projection_adjunct
    {D E : Type*} [Category* D] [Category* E]
    (L : D ⥤ E) (V : E ⥤ D) (adj : L ⊣ V)
    (T : D × D ⥤ D) (T' : E × E ⥤ E)
    (θ : (V.prod V) ⋙ T ⟶ T' ⋙ V) (X : D) (Y : E) :
    adj.homEquiv _ _
      (((adj.projectionMap V (Functor.curry.obj T) (Functor.curry.obj T')
        ((Functor.curryObjProdComp V V T).inv ≫ Functor.curry.map θ)).app X).app Y) =
      T.map (CategoryTheory.Prod.mkHom (adj.unit.app X) (𝟙 (V.obj Y))) ≫
        θ.app (L.obj X, Y) := by
  rw [Adjunction.projectionMap_app_app, Equiv.apply_symm_apply]
  change T.map (CategoryTheory.Prod.mkHom (adj.unit.app X) (𝟙 _)) ≫
    (𝟙 _ ≫ θ.app (L.obj X, Y)) = _
  rw [Category.id_comp]

private theorem open_tensor_formula (R : Sheaf J CommRingCat.{u + 1}) (U : C)
    (hU : ∀ W : C, Subsingleton (W ⟶ U))
    (a : TensorModel R) (b : TensorModel (R.over U)) (r : Restriction R U)
    (t : openTensorRestrictionComparison R U a b r) :
    openTensorFormula R U a b r t := by
  let : HasDerivedCategory (Mod R) :=
    AlgebraicGeometry.Scheme.ProjectionRestriction.derived R
  let : HasDerivedCategory (Mod (R.over U)) :=
    AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOver R U
  classical
  let : (localizedModuleRestriction R U).Additive := localizedModuleRestriction_additive R U
  let L := (localizedModuleExtension R U).mapDerivedCategory
  let V := (localizedModuleRestriction R U).mapDerivedCategory
  let adj := localizedModuleDerivedAdjunction R U
  let : IsIso adj.unit := derived_open_unit_iso R U hU
  let δ := (Functor.curryObjProdComp V V b.functor).inv ≫
    Functor.curry.map t.comparison.inv
  let T := Functor.curry.obj b.functor
  let T' := Functor.curry.obj a.functor
  have : IsIso δ := inferInstance
  let α := adj.projectionMap V T T' δ
  have hα (E : Der (R.over U)) (F : Der R) : IsIso ((α.app E).app F) := by
    obtain ⟨Z, ⟨e⟩⟩ := tensor_supported R U a E F
    exact adj.isIso_projectionMap_app_app_of_iso V T T' δ E F Z e
  have (E : Der (R.over U)) : IsIso (α.app E) := NatIso.isIso_of_isIso_app _
  have : IsIso α := NatIso.isIso_of_isIso_app _
  obtain ⟨β₀, hβ₀⟩ := uncurry_projection_iso L V b.functor a.functor α
  let i := (𝟭 (Der (R.over U))).prod (openTensorCoefficients R).ι
  let β : openTensorSource R U a ≅ openTensorTarget R U b :=
    Functor.isoWhiskerLeft i β₀
  change ∃! β : openTensorSource R U a ≅ openTensorTarget R U b, _
  have hβ (E : Der (R.over U)) (F : (openTensorCoefficients R).FullSubcategory) :
      adj.homEquiv _ _ (β.inv.app (E, F)) =
        b.functor.map (CategoryTheory.Prod.mkHom (adj.unit.app E) (𝟙 _)) ≫
          t.comparison.inv.app (L.obj E, F.obj) := by
    change adj.homEquiv _ _ (β₀.inv.app (E, F.obj)) = _
    rw [hβ₀]
    exact uncurried_projection_adjunct L V adj b.functor a.functor t.comparison.inv E F.obj
  refine ⟨β, hβ, ?_⟩
  intro γ hγ
  have hh : γ.symm = β.symm := by
    apply Iso.ext
    apply NatTrans.ext
    funext ⟨E, F⟩
    exact (adj.homEquiv _ _).injective ((hγ E F).trans (hβ E F).symm)
  exact congrArg Iso.symm hh


/-- The canonical open tensor map is an isomorphism, natural in both derived variables.
The equation characterizes its inverse as the adjunction projection map: its adjunct
is the unit tensored with the restricted coefficient, followed by the inverse of the
canonical restriction-tensor comparison. Thus the direction and normalization are fixed.
The open site is presented on the slice at `ProEt.mk c.i`, with the restricted ring R;
no comparison with any independently chosen coefficient sheaf occurs.

Source: blueprint lemma 1269; Stacks 03DI, 03DJ, 03EL, 06YQ and 07A4
(blueprint: lemma-weil-pbc-projection-formula-open-piece).

Proof:
1. The open immersion is a monomorphism, so its slice object is subterminal.
   Its extension-restriction adjunction unit is invertible: the presheaf extension
   is a direct sum over a singleton, and sheafification is locally bijective.
   Exact localization carries this to an invertible derived unit.
2. The ordinary slice extension-tensor comparison lifts through bicomplex
   totalization, since extension is additive and preserves coproducts.
3. Resolve a coefficient by a flat K-flat complex. The TensorModel representative
   comparison and the mapping-cone tensor/flip isomorphisms show that a tensor
   with one K-flat factor is computed by the total tensor complex. Thus the
   derived tensor of an extension lies in the essential image of extension.
4. The categorical adjunction projection-map criterion makes the canonical
   projection transformation invertible. Uncurry it and restrict to strict-perfect
   coefficients. Its adjunct is the unit followed by the specified inverse tensor
   comparison. Adjunction bijectivity proves uniqueness. -/
theorem openImmersionTensor_iso {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) [QuasiCompact c.i]
    (R : Sheaf (ProEt.topology c.Z) CommRingCat.{u + 1})
    (a : TensorModel R) (b : TensorModel (R.over (ProEt.mk c.i)))
    (r : Restriction R (ProEt.mk c.i))
    (t : openTensorRestrictionComparison R (ProEt.mk c.i) a b r) :
    openTensorFormula R (ProEt.mk c.i) a b r t := by
  have hU (W : c.Z.ProEt) : Subsingleton (W ⟶ ProEt.mk c.i) := by
    constructor
    intro f g
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono c.i).1
    exact f.w.trans g.w.symm
  exact open_tensor_formula R (ProEt.mk c.i) hU a b r t

end SheafOfModules
