/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.QlbarInternalHomCoefficientComparison
public import Sheaf.Paper.InternalSectionTotalComparison
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.InternalSectionModuleFlat
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.ModuleObjects.Free

/-! # Finite-subextension tensor models with a common lower bound

Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), proof preceding (5.4), and
paragraph preceding Lemma 5.6 (blueprint: lem-sfb-qlbar-bounded-tensor-colimit).

The coefficient diagram and cocone below use the actual field inclusions.
Tensor on complexes is degreewise tensor, with no K-flatness imposed on its
second input. Derived tensor is the existing ringed-site K-flat localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
-- Avoid replaying the concrete sheaf functor calculations during tactic linting.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false

universe u u₁ v₁ u₂ v₂ u₃ v₃
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.QlbarBoundedTensor
open Scheme PadicAlgCl ModuleObjectRingedComparison

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- Degreewise tensor with a complex, functorially in its coefficient module.
Source: HRS proof of Lemma 5.3(1), tensor models
(blueprint: lem-sfb-qlbar-bounded-tensor-colimit). -/
def tensorComplex (E : FiniteIntermediateField ℓ)
    (K : CochainComplex (Modules (Profinite.continuousMapRingObj E) X) ℤ) :
    Modules (Profinite.continuousMapRingObj E) X ⥤
      CochainComplex (Modules (Profinite.continuousMapRingObj E) X) ℤ where
  obj P := ((tensorLeft P).mapHomologicalComplex (.up ℤ)).obj K
  map q := (NatTrans.mapHomologicalComplex ((curriedTensor _).map q) (.up ℤ)).app K
  map_id P := by
    ext r
    simp
  map_comp f g := by
    ext r
    simp

/-- The existing derived tensor, specialized to the reconstructed coefficient ring.
This is an abbreviation for the dependency's functor, with no new choice or tensor.
Source: Stacks 06YU; HRS tensor realization
(blueprint: lem-sfb-qlbar-bounded-tensor-colimit). -/
abbrev derivedTensor (E : FiniteIntermediateField ℓ) :=
  SheafOfModules.siteDerivedTensorIndependentCoefficients
    (ProEt.topology X) (ring (Profinite.continuousMapRingObj E) X)

/-- The prescribed finite-field tensor cocone for a chosen representative.
Source: HRS proof preceding (5.4), coefficient union before Lemma 5.6
(blueprint: lem-sfb-qlbar-bounded-tensor-colimit). -/
def tensorCocone (E : FiniteIntermediateField ℓ)
    (K : CochainComplex (Modules (Profinite.continuousMapRingObj E) X) ℤ) :=
  (tensorComplex X ℓ E K).mapCocone (QlbarInternalHom.coefficientCocone X ℓ E)

/-- The actual degreewise tensor diagram represents derived scalar extension.
The isomorphisms retain both finite-field transitions and the closure legs.
Source: HRS proof preceding (5.4), Stacks 06YU
(blueprint: lem-sfb-qlbar-bounded-tensor-colimit). -/
def Represents (E : FiniteIntermediateField ℓ)
    (A : DerivedCategory (Modules (Profinite.continuousMapRingObj E) X))
    (K : CochainComplex (Modules (Profinite.continuousMapRingObj E) X) ℤ) : Prop :=
  (∀ r : ℤ, Nonempty (IsColimit
    ((HomologicalComplex.eval _ _ r).mapCocone (tensorCocone X ℓ E K)))) ∧
  ∃ (e : ∀ i : AsSmall.{u + 1} (Under E),
      DerivedCategory.Q.obj
          ((tensorComplex X ℓ E K).obj ((QlbarInternalHom.coefficients X ℓ E).obj i)) ≅
        (derivedTensor X ℓ E).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((QlbarInternalHom.coefficients X ℓ E).obj i), A))
    (b : DerivedCategory.Q.obj (tensorCocone X ℓ E K).pt ≅
      (derivedTensor X ℓ E).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (QlbarInternalHom.coefficientCocone X ℓ E).pt, A)),
    (∀ (i j : AsSmall.{u + 1} (Under E)) (h : i ⟶ j),
      DerivedCategory.Q.map ((tensorComplex X ℓ E K).map
          ((QlbarInternalHom.coefficients X ℓ E).map h)) ≫ (e j).hom =
        (e i).hom ≫ (derivedTensor X ℓ E).map
          ((DerivedCategory.singleFunctor _ 0).map
            ((QlbarInternalHom.coefficients X ℓ E).map h), 𝟙 A)) ∧
    (∀ i : AsSmall.{u + 1} (Under E),
      DerivedCategory.Q.map ((tensorCocone X ℓ E K).ι.app i) ≫ b.hom =
        (e i).hom ≫ (derivedTensor X ℓ E).map
          ((DerivedCategory.singleFunctor _ 0).map
            ((QlbarInternalHom.coefficientCocone X ℓ E).ι.app i), 𝟙 A))

/-- Colimit, finite freeness and flatness of the specified coefficient sheaves.
Finite freeness uses the regular module, transported by the fixed equivalence.
Source: HRS before Lemma 5.6, Stacks 03EU
(blueprint: lem-sfb-qlbar-bounded-tensor-colimit). -/
def CoefficientFacts (E : FiniteIntermediateField ℓ) : Prop :=
  Nonempty (IsColimit (QlbarInternalHom.coefficientCocone X ℓ E)) ∧
  (∀ i : AsSmall.{u + 1} (Under E),
    (∃ n : ℕ, Nonempty
      ((equivalence (Profinite.continuousMapRingObj E) X).functor.obj
        (Mod.finiteFree (padicSubfieldRingObj X ℓ E) n) ≅
          (QlbarInternalHom.coefficients X ℓ E).obj i)) ∧
    SheafOfModules.IsFlatOnSite
      (R := ring (Profinite.continuousMapRingObj E) X)
      ((QlbarInternalHom.coefficients X ℓ E).obj i)) ∧
  SheafOfModules.IsFlatOnSite (R := ring (Profinite.continuousMapRingObj E) X)
    (QlbarInternalHom.coefficientCocone X ℓ E).pt

/-- Canonical section-ring pullback, through the already recorded exact equivalence.
Source: untwisted Cartesian coefficients and their coefficient-change squares
(blueprint: lem-sfb-qlbar-bounded-tensor-colimit). -/
abbrev pullback (E : FiniteIntermediateField ℓ) {Y : Scheme.{u}} (f : X ⟶ Y) :=
  (equivalence (Profinite.continuousMapRingObj E) Y).inverse ⋙
    CondensedRing.upperStar (Profinite.continuousMapRingObj E) f ⋙
      (equivalence (Profinite.continuousMapRingObj E) X).functor

attribute [local irreducible] QlbarInternalHom.coefficients QlbarInternalHom.coefficientCocone
  SheafOfModules.siteDerivedTensorIndependentCoefficients

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  CategoryTheory.Sheaf.monoidalCategory monoidal_upperStar oplaxMonoidal_upperStar
  SheafOfModules.monoidalCategory

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] CategoryTheory.Sheaf.symmetricCategory

private instance cachedAbelianSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) Ab.{u + 1} := inferInstance
private instance cachedAbelianWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology T) Ab.{u + 1} := inferInstance

private instance cachedRingWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology T) RingCat.{u + 1} := inferInstance
private instance cachedTypeWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology T) (Type (u + 1)) := inferInstance

private theorem coefficients_colimit (E : FiniteIntermediateField ℓ) :
    Nonempty (IsColimit (QlbarInternalHom.coefficientCocone X ℓ E)) := by
  classical
  obtain ⟨s, b, hs, hb⟩ := QlbarInternalHom.coefficientModules X ℓ E
  let U := SheafOfModules.toSheaf
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (ring (Profinite.continuousMapRingObj E) X))
  let e : QlbarInternalHom.coefficients X ℓ E ⋙ U ≅
      (QlbarInternalHom.fields ℓ E) ⋙
        (Profinite.padicSubfieldRingObjFunctor ℓ ⋙ upperStarFromPoint X) :=
    NatIso.ofComponents (fun i ↦ U.mapIso (s i)) (by
      intro i j h
      ext V x
      exact hs i j h V x)
  have hf := (QlbarInternalHom.fieldDiagram.{u, u} X ℓ E).2.1
  have hcol := (Functor.Final.isColimitWhiskerEquiv (QlbarInternalHom.fields ℓ E)
    (padicAlgClRingObjCocone X ℓ)).symm (isColimitPadicAlgClRingObjCocone X ℓ)
  have hcol' := (IsColimit.precomposeHomEquiv e _).symm hcol
  have : HasColimit (QlbarInternalHom.coefficients X ℓ E) := inferInstance
  have : ReflectsColimit (QlbarInternalHom.coefficients X ℓ E) U :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  let c' := (Cocone.precompose e.hom).obj
    ((padicAlgClRingObjCocone X ℓ).whisker (QlbarInternalHom.fields ℓ E))
  have ec : U.mapCocone (QlbarInternalHom.coefficientCocone X ℓ E) ≅ c' :=
    Cocone.ext (U.mapIso b) (by
      intro i
      ext V x
      exact hb i V x)
  exact ⟨isColimitOfReflects U (hcol'.ofIsoColimit ec.symm)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem finite_free_flat (E : FiniteIntermediateField ℓ) (n : ℕ) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
      (R := ring (Profinite.continuousMapRingObj E) X)
      ((equivalence (Profinite.continuousMapRingObj E) X).functor.obj
        (Mod.finiteFree (padicSubfieldRingObj X ℓ E) n)) := by
  let R := padicSubfieldRingObj X ℓ E
  have hf : ObjectProperty.flat (Mod.finiteFree R n) :=
    ObjectProperty.flat_of_isDualizable (isDualizable_biproduct_unit n)
  exact (InternalAbelianSheafModule.flat_iff_sectionModule (ProEt.topology X) R _).1 hf

private theorem coefficient_finite_free (E : FiniteIntermediateField ℓ) :
    ∀ i : AsSmall.{u + 1} (Under E), ∃ n : ℕ, Nonempty
      ((equivalence (Profinite.continuousMapRingObj E) X).functor.obj
        (Mod.finiteFree (padicSubfieldRingObj X ℓ E) n) ≅
          (QlbarInternalHom.coefficients X ℓ E).obj i) := by
  intro i
  obtain ⟨s, _, _, _⟩ := QlbarInternalHom.coefficientModules X ℓ E
  obtain ⟨n, ⟨e⟩⟩ := (QlbarInternalHom.fieldDiagram.{u, u} X ℓ E).2.2
    ((QlbarInternalHom.fields ℓ E).obj i)
    (leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom))
  exact ⟨n, ⟨(equivalence (Profinite.continuousMapRingObj E) X).functor.mapIso e ≪≫
    (s i).symm⟩⟩

private theorem coefficient_flat (E : FiniteIntermediateField ℓ)
    (i : AsSmall.{u + 1} (Under E)) :
    SheafOfModules.IsFlatOnSite
      (J := ProEt.topology X) (R := ring (Profinite.continuousMapRingObj E) X)
      ((QlbarInternalHom.coefficients X ℓ E).obj i) := by
  obtain ⟨n, ⟨e⟩⟩ := coefficient_finite_free X ℓ E i
  have hf := finite_free_flat X ℓ E n
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso (ring (Profinite.continuousMapRingObj E) X) _).symm
    ((exactFunctor _ _).prop_of_iso ((curriedTensor _).flip.mapIso e)
      ((exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso (ring (Profinite.continuousMapRingObj E) X) _)
        hf))

private theorem tensorLeft_colimit_exact
    {I C : Type*} [Category* I] [Category* C] [MonoidalCategory C]
    [HasColimitsOfShape I C] [HasExactColimitsOfShape I C]
    (F : I ⥤ C) (c : Cocone F) (hc : IsColimit c)
    (hl : ∀ i, PreservesFiniteLimits (tensorLeft (F.obj i)))
    (hr : ∀ M, PreservesColimit F (tensorRight M)) :
    PreservesFiniteLimits (tensorLeft c.pt) := by
  have : PreservesColimit F (curriedTensor C) :=
    preservesColimit_of_evaluation _ _ fun M ↦ hr M
  let e : tensorLeft c.pt ≅ (F ⋙ curriedTensor C).flip ⋙ colim :=
    (curriedTensor C).mapIso (hc.coconePointUniqueUpToIso (colimit.isColimit F)) ≪≫
      preservesColimitIso (curriedTensor C) F ≪≫ colimitIsoFlipCompColim _
  have : PreservesFiniteLimits ((F ⋙ curriedTensor C).flip) :=
    preservesFiniteLimits_of_evaluation _ fun i ↦ hl i
  exact preservesFiniteLimits_of_natIso e.symm

private theorem flat_module_colimit
    {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{u₂} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u₂})
    {I : Type u₂} [SmallCategory I]
    [HasColimitsOfShape I (SheafOfModules.KFlatFixedTensor.Modules R)]
    [HasExactColimitsOfShape I (SheafOfModules.KFlatFixedTensor.Modules R)]
    (F : I ⥤ SheafOfModules.KFlatFixedTensor.Modules R) (c : Cocone F)
    (hcol : IsColimit c)
    (hflat : ∀ i, SheafOfModules.IsFlatOnSite (J := J) (R := R) (F.obj i)) :
    SheafOfModules.IsFlatOnSite (J := J) (R := R) c.pt := by
  have : J.HasSheafCompose (forget₂ CommRingCat.{u₂} RingCat.{u₂}) := inferInstance
  let : MonoidalCategory (SheafOfModules.KFlatFixedTensor.Modules R) :=
    SheafOfModules.cochainModulesMonoidal R
  let : SymmetricCategory (SheafOfModules.KFlatFixedTensor.Modules R) :=
    SheafOfModules.cochainModulesSymmetric R
  let A := SheafOfModules.KFlatFixedTensor.Modules R
  have hleft (i : I) :
      PreservesFiniteLimits (tensorLeft (F.obj i)) := by
    have hs : PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight (A := R) (F.obj i)) :=
      (hflat i).1
    have : PreservesFiniteLimits (tensorRight (F.obj i)) :=
      preservesFiniteLimits_of_natIso (SheafOfModules.siteSheafTensorRightIso R _)
    exact preservesFiniteLimits_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight (F.obj i)).symm
  have ht (M : A) : PreservesColimitsOfSize.{u₂, u₂} (tensorRight M) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have : PreservesFiniteLimits (tensorLeft c.pt) :=
    tensorLeft_colimit_exact F c hcol hleft (fun M ↦ inferInstance)
  have : PreservesFiniteLimits (tensorRight c.pt) :=
    preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight c.pt)
  have : PreservesFiniteColimits (tensorRight c.pt) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have hresult : SheafOfModules.IsFlatOnSite (J := J) (R := R) c.pt :=
    ⟨preservesFiniteLimits_of_natIso (SheafOfModules.siteSheafTensorRightIso R _).symm,
      preservesFiniteColimits_of_natIso (SheafOfModules.siteSheafTensorRightIso R _).symm⟩
  exact hresult

private theorem coefficient_facts (E : FiniteIntermediateField ℓ) :
    CoefficientFacts X ℓ E := by
  classical
  obtain ⟨hcol⟩ := coefficients_colimit X ℓ E
  have : IsFiltered (AsSmall.{u + 1} (Under E)) :=
    (QlbarInternalHom.fieldDiagram.{u, u} X ℓ E).1
  have : HasExactColimitsOfShape (AsSmall.{u + 1} (Under E))
      (Modules (Profinite.continuousMapRingObj E) X) :=
    HasExactColimitsOfShape.domain_of_functor _ (SheafOfModules.toSheaf _)
  exact ⟨⟨hcol⟩, fun i ↦ ⟨coefficient_finite_free X ℓ E i,
    coefficient_flat X ℓ E i⟩,
    flat_module_colimit (ring (Profinite.continuousMapRingObj E) X)
      (QlbarInternalHom.coefficients X ℓ E) _ hcol (coefficient_flat X ℓ E)⟩


private def restrictedRegularPullback
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    (U : C ⥤ D) [U.LaxMonoidal]
    {R S : C} [MonObj R] [MonObj S]
    {R' S' : D} [MonObj R'] [MonObj S']
    (s : R ⟶ S) [IsMonHom s] (t : R' ⟶ S') [IsMonHom t]
    (a : U.obj R ≅ R') [IsMonHom a.hom]
    (b : U.obj S ≅ S') [IsMonHom b.hom]
    (h : U.map s ≫ b.hom = a.hom ≫ t) :
    (Mod.comap a.inv).obj ((U.mapMod R).obj ((Mod.comap s).obj (Mod.regular S))) ≅
      (Mod.comap t).obj (Mod.regular S') := by
  have hab : a.inv ≫ U.map s ≫ b.hom = t := by
    rw [h, Iso.inv_hom_id_assoc]
  refine (Mod.comap a.inv).mapIso ((U.mapModComapIso s).app (Mod.regular _)) ≪≫ ?_
  refine Mod.isoMk b ?_
  change (a.inv ▷ _ ≫ (U.map s ▷ _ ≫ μ[U.obj S])) ≫ b.hom =
    _ ◁ b.hom ≫ t ▷ _ ≫ μ[S']
  simp only [Category.assoc]
  rw [IsMonHom.mul_hom, tensorHom_def']
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc, ← comp_whiskerRight_assoc,
    whisker_exchange_assoc, ← comp_whiskerRight_assoc, hab]
  rw [whisker_exchange_assoc]

open MonObj in
private def restrictedMap
    {D : Type*} [Category* D] [MonoidalCategory D]
    {R A B : D} [MonObj R] [MonObj A] [MonObj B]
    (sA : R ⟶ A) (sB : R ⟶ B) [IsMonHom sA] [IsMonHom sB]
    (g : A ⟶ B) [IsMonHom g] (h : sA ≫ g = sB) :
    (Mod.comap sA).obj (Mod.regular A) ⟶ (Mod.comap sB).obj (Mod.regular B) := by
  refine Mod.homMk g ?_
  change (sA ▷ A ≫ μ[A]) ≫ g = R ◁ g ≫ sB ▷ B ≫ μ[B]
  rw [Category.assoc, IsMonHom.mul_hom, tensorHom_def']
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc, ← comp_whiskerRight_assoc, h]

set_option backward.isDefEq.respectTransparency false in
private def nativeDiagram (E : FiniteIntermediateField ℓ) :
    AsSmall.{u + 1} (Under E) ⥤ Internal (Profinite.continuousMapRingObj E) X where
  obj i := (Mod.comap (padicSubfieldRingObjMap X ℓ
    (leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom)))).obj
      (Mod.regular (padicSubfieldRingObj X ℓ ((QlbarInternalHom.fields ℓ E).obj i)))
  map {i j} g := restrictedMap _ _
    (padicSubfieldRingObjMap X ℓ (leOfHom ((QlbarInternalHom.fields ℓ E).map g)))
    (coefficientComplex_ringMap_comp X ℓ _ _)
  map_id i := by
    apply Mod.hom_ext
    change (upperStarFromPoint X).map (Profinite.padicSubfieldRingObjMap ℓ _) = 𝟙 _
    rw [Profinite.padicSubfieldRingObjMap_id]
    exact (upperStarFromPoint X).map_id _
  map_comp f g := by
    apply Mod.hom_ext
    exact (coefficientComplex_ringMap_comp X ℓ _ _).symm

open MonObj in
private theorem restrictedRegularPullback_exists
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    (U : C ⥤ D) [U.LaxMonoidal]
    {R S : C} [MonObj R] [MonObj S]
    {R' S' : D} [MonObj R'] [MonObj S']
    (s : R ⟶ S) [IsMonHom s] (t : R' ⟶ S') [IsMonHom t]
    (a : U.obj R ≅ R') [IsMonHom a.hom]
    (b : U.obj S ≅ S') [IsMonHom b.hom]
    (h : U.map s ≫ b.hom = a.hom ≫ t) :
    ∃ e : (Mod.comap a.inv).obj ((U.mapMod R).obj
        ((Mod.comap s).obj (Mod.regular S))) ≅
          (Mod.comap t).obj (Mod.regular S'), e.hom.hom = b.hom := by
  refine ⟨restrictedRegularPullback U s t a b h, ?_⟩
  change 𝟙 _ ≫ b.hom = b.hom
  exact Category.id_comp _

open MonObj in
private theorem nativeStage_exists (E F : FiniteIntermediateField ℓ) (h : E ≤ F)
    {Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ e : (cartesianCoefficientLift (Profinite.continuousMapRingObj E) f).obj
        ((Mod.comap (padicSubfieldRingObjMap Y ℓ h)).obj
          (Mod.regular (padicSubfieldRingObj Y ℓ F))) ≅
      (Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj
        (Mod.regular (padicSubfieldRingObj X ℓ F)),
      e.hom.hom = condensedPullbackHom (Profinite.continuousMapRingObj F) f := by
  exact restrictedRegularPullback_exists
    (AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f)
    (padicSubfieldRingObjMap Y ℓ h) (padicSubfieldRingObjMap X ℓ h)
    (asIso (condensedPullbackHom (Profinite.continuousMapRingObj E) f))
    (asIso (condensedPullbackHom (Profinite.continuousMapRingObj F) f))
    (map_coefficientMap_comp_condensedPullbackHom (Profinite.padicSubfieldRingObjMap ℓ h) f)

private theorem coefficient_native_iso (E : FiniteIntermediateField ℓ) :
    Nonempty (QlbarInternalHom.coefficients X ℓ E ≅
      nativeDiagram X ℓ E ⋙ (equivalence (Profinite.continuousMapRingObj E) X).functor) := by
  obtain ⟨s, _, hs, _⟩ := QlbarInternalHom.coefficientModules X ℓ E
  refine ⟨NatIso.ofComponents (fun i ↦ ?_) ?_⟩
  · exact s _
  · intro i j g
    ext V x
    exact hs i j g V x

set_option backward.isDefEq.respectTransparency false in
private theorem nativeDiagram_pullback (E : FiniteIntermediateField ℓ)
    {Y : Scheme.{u}} (f : X ⟶ Y) :
    Nonempty (nativeDiagram Y ℓ E ⋙
      cartesianCoefficientLift (Profinite.continuousMapRingObj E) f ≅ nativeDiagram X ℓ E) := by
  classical
  have h (i : AsSmall.{u + 1} (Under E)) := nativeStage_exists X ℓ E
    ((QlbarInternalHom.fields ℓ E).obj i)
    (leOfHom (((AsSmall.equiv (C := Under E)).inverse.obj i).hom)) f
  choose e he using h
  refine ⟨NatIso.ofComponents (fun i ↦ ?_) ?_⟩
  · exact e _
  · intro i j g
    refine Mod.hom_ext _ _ ?_
    change (AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f).map _ ≫ (e j).hom.hom =
      (e i).hom.hom ≫ _
    let qY := padicSubfieldRingObjMap Y ℓ
      (leOfHom ((QlbarInternalHom.fields ℓ E).map g))
    let qX := padicSubfieldRingObjMap X ℓ
      (leOfHom ((QlbarInternalHom.fields ℓ E).map g))
    let U := AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f
    exact (congrArg (fun b ↦ U.map qY ≫ b) (he j)).trans
      ((map_coefficientMap_comp_condensedPullbackHom
        (Profinite.padicSubfieldRingObjMap.{u} ℓ
          (leOfHom ((QlbarInternalHom.fields ℓ E).map g))) f).trans
        (congrArg (fun a ↦ a ≫ qX) (he i)).symm)

private theorem colimit_transport
    {I C D : Type*} [Category* I] [Category* C] [Category* D]
    {F : I ⥤ C} {G : I ⥤ D} (L : C ⥤ D) (c : Cocone F) (d : Cocone G)
    (p : F ⋙ L ≅ G) [PreservesColimit F L]
    (hc : IsColimit c) (hd : IsColimit d) :
    ∃ b : L.obj c.pt ≅ d.pt, ∀ i,
      L.map (c.ι.app i) ≫ b.hom = p.hom.app i ≫ d.ι.app i := by
  let hY := isColimitOfPreserves L hc
  let hX := (IsColimit.precomposeHomEquiv p d).symm hd
  exact ⟨hY.coconePointUniqueUpToIso hX,
    hY.comp_coconePointUniqueUpToIso_hom hX⟩

private theorem equivalence_pullback_iso
    {I C D A B : Type*} [Category* I] [Category* C] [Category* D]
    [Category* A] [Category* B]
    (EC : C ≌ A) (ED : D ≌ B) (U : C ⥤ D)
    (F : I ⥤ C) (G : I ⥤ D) (P : I ⥤ A) (Q : I ⥤ B)
    (e : P ≅ F ⋙ EC.functor) (e' : Q ≅ G ⋙ ED.functor)
    (n : F ⋙ U ≅ G) :
    Nonempty (P ⋙ (EC.inverse ⋙ U ⋙ ED.functor) ≅ Q) :=
  ⟨Functor.isoWhiskerRight e _ ≪≫
    Functor.isoWhiskerLeft F
      (Functor.isoWhiskerRight EC.unitIso.symm (U ⋙ ED.functor)) ≪≫
    Functor.isoWhiskerRight n ED.functor ≪≫ e'.symm⟩

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_coefficients (E : FiniteIntermediateField ℓ)
    {Y : Scheme.{u}} (f : X ⟶ Y)
    (hXc : Nonempty (IsColimit (QlbarInternalHom.coefficientCocone X ℓ E)))
    (hYc : Nonempty (IsColimit (QlbarInternalHom.coefficientCocone Y ℓ E))) :
    ∃ (p : QlbarInternalHom.coefficients Y ℓ E ⋙ pullback X ℓ E f ≅
          QlbarInternalHom.coefficients X ℓ E)
      (b : (pullback X ℓ E f).obj (QlbarInternalHom.coefficientCocone Y ℓ E).pt ≅
        (QlbarInternalHom.coefficientCocone X ℓ E).pt),
      ∀ i : AsSmall.{u + 1} (Under E),
        (pullback X ℓ E f).map ((QlbarInternalHom.coefficientCocone Y ℓ E).ι.app i) ≫ b.hom =
          p.hom.app i ≫ (QlbarInternalHom.coefficientCocone X ℓ E).ι.app i := by
  classical
  let EY := equivalence (Profinite.continuousMapRingObj E) Y
  let EX := equivalence (Profinite.continuousMapRingObj E) X
  let L := pullback X ℓ E f
  let FY := nativeDiagram Y ℓ E
  let FX := nativeDiagram X ℓ E
  obtain ⟨eY⟩ := coefficient_native_iso Y ℓ E
  obtain ⟨eX⟩ := coefficient_native_iso X ℓ E
  obtain ⟨n⟩ := nativeDiagram_pullback X ℓ E f
  have hp : Nonempty (QlbarInternalHom.coefficients Y ℓ E ⋙ L ≅
      QlbarInternalHom.coefficients X ℓ E) :=
    equivalence_pullback_iso EY EX
      (CondensedRing.upperStar (Profinite.continuousMapRingObj E) f)
      FY FX _ _ eY eX
      (Functor.isoWhiskerLeft FY
        (cartesianCoefficientPullbackIso (Profinite.continuousMapRingObj E) f) ≪≫ n)
  obtain ⟨p⟩ := hp
  have hb := colimit_transport L
    (QlbarInternalHom.coefficientCocone Y ℓ E)
    (QlbarInternalHom.coefficientCocone X ℓ E) p hYc.some hXc.some
  refine ⟨p, ?_⟩
  exact hb


attribute [local instance 30000] HasDerivedCategory.ofIsGrothendieckAbelian

private theorem tensor_strict (E : FiniteIntermediateField ℓ)
    (K : CochainComplex (Modules (Profinite.continuousMapRingObj E) X) ℤ)
    (a : ℤ) [K.IsStrictlyGE a] (P : Modules (Profinite.continuousMapRingObj E) X) :
    ((tensorComplex X ℓ E K).obj P).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact Functor.map_isZero (tensorLeft P) (K.isZero_of_isStrictlyGE a i hi)

private theorem tensor_colimit (E : FiniteIntermediateField ℓ)
    (K : CochainComplex (Modules (Profinite.continuousMapRingObj E) X) ℤ)
    (hc : IsColimit (QlbarInternalHom.coefficientCocone X ℓ E)) :
    ∀ r : ℤ, Nonempty (IsColimit
      ((HomologicalComplex.eval _ _ r).mapCocone (tensorCocone X ℓ E K))) := by
  intro r
  have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients
    (ring (Profinite.continuousMapRingObj E) X) (K.X r)
  have : PreservesColimitsOfSize.{u + 1, u + 1} (tensorRight (K.X r)) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (K.X r))
  exact ⟨isColimitOfPreserves (tensorRight (K.X r)) hc⟩

private theorem tensor_homology_colimit (E : FiniteIntermediateField ℓ)
    (K : CochainComplex (Modules (Profinite.continuousMapRingObj E) X) ℤ)
    [IsFiltered (AsSmall.{u + 1} (Under E))]
    (hc : ∀ r : ℤ, Nonempty (IsColimit
      ((HomologicalComplex.eval _ _ r).mapCocone (tensorCocone X ℓ E K)))) (q : ℤ) :
    Nonempty (IsColimit
      ((DerivedCategory.Q.{u + 1} ⋙ DerivedCategory.homologyFunctor.{u + 1} _ q).mapCocone
        (tensorCocone X ℓ E K))) := by
  have : HasExactColimitsOfShape (AsSmall.{u + 1} (Under E))
      (Modules (Profinite.continuousMapRingObj E) X) :=
    HasExactColimitsOfShape.domain_of_functor _ (SheafOfModules.toSheaf _)
  let h := HomologicalComplex.isColimitOfEval _ _ (fun r ↦ (hc r).some)
  exact ⟨IsColimit.mapCoconeEquiv (DerivedCategory.homologyFunctorFactors.{u + 1} _ q).symm
    (isColimitOfPreserves (HomologicalComplex.homologyFunctor _ _ q) h)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem collapse_inv_natural
    {C₁ : Type u₁} [Category.{v₁} C₁] [HasZeroMorphisms C₁] [HasZeroObject C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [HasZeroMorphisms C₂]
    {D : Type u₃} [Category.{v₃} D] [Preadditive D] [HasZeroObject D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ P, (F.obj P).PreservesZeroMorphisms]
    (K : CochainComplex C₂ ℤ) {P P' : C₁} (g : P ⟶ P') :
    (CochainComplex.mapBifunctorSingle₁Iso F P K).inv ≫
      HomologicalComplex.mapBifunctorMap
        ((HomologicalComplex.single _ (.up ℤ) 0).map g) (𝟙 K) F (.up ℤ) =
    (NatTrans.mapHomologicalComplex (F.map g) (.up ℤ)).app K ≫
      (CochainComplex.mapBifunctorSingle₁Iso F P' K).inv := by
  apply HomologicalComplex.Hom.ext
  funext r
  dsimp only [HomologicalComplex.comp_f]
  rw [CochainComplex.mapBifunctorSingle₁Iso_inv_f,
    CochainComplex.mapBifunctorSingle₁Iso_inv_f]
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.single_map_f_self]
  simp

set_option backward.isDefEq.respectTransparency false in
private def collapse_natIso
    {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
    (F : C ⥤ C ⥤ C) [F.PreservesZeroMorphisms]
    [∀ P, (F.obj P).PreservesZeroMorphisms]
    [∀ (K L : CochainComplex C ℤ), CochainComplex.HasMapBifunctor K L F]
    (V : CochainComplex C ℤ) :
    { obj := fun P ↦ ((F.obj P).mapHomologicalComplex (.up ℤ)).obj V
      map := fun g ↦ (NatTrans.mapHomologicalComplex (F.map g) (.up ℤ)).app V
      map_id := by intro P; ext r; simp
      map_comp := by intro P P' P'' g h; ext r; simp } ≅
      (CochainComplex.singleFunctor C 0) ⋙ F.map₂CochainComplex.flip.obj V :=
  NatIso.ofComponents
    (fun P ↦ (CochainComplex.mapBifunctorSingle₁Iso F P V).symm)
    (fun g ↦ (collapse_inv_natural F V g).symm)

private theorem iso_family_of_trans
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G H : C ⥤ D} (t : F ⟶ G) (d : F ≅ H) (P : C → Prop)
    (ht : ∀ X, P X → IsIso (t.app X)) :
    ∃ e : ∀ X, P X → (G.obj X ≅ H.obj X),
      ∀ X Y (hX : P X) (hY : P Y) (g : X ⟶ Y),
        G.map g ≫ (e Y hY).hom = (e X hX).hom ≫ H.map g := by
  let e (X : C) (hX : P X) : G.obj X ≅ H.obj X := by
    have := ht X hX
    exact (asIso (t.app X)).symm ≪≫ d.app X
  refine ⟨e, ?_⟩
  intro X Y hX hY g
  have := ht X hX
  have := ht Y hY
  dsimp only [e, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  apply (cancel_epi (t.app X)).1
  simp only [Category.assoc]
  rw [← Category.assoc, ← t.naturality g]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  exact d.hom.naturality g

private def termwiseBifunctor
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    (F : C ⥤ C ⥤ C) [∀ P, (F.obj P).PreservesZeroMorphisms]
    (K : CochainComplex C ℤ) : C ⥤ CochainComplex C ℤ where
  obj P := ((F.obj P).mapHomologicalComplex (.up ℤ)).obj K
  map g := (NatTrans.mapHomologicalComplex (F.map g) (.up ℤ)).app K
  map_id P := by ext r; simp
  map_comp f g := by ext r; simp

private def termwise_map
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    (F : C ⥤ C ⥤ C) [∀ P, (F.obj P).PreservesZeroMorphisms]
    {V K : CochainComplex C ℤ} (p : V ⟶ K) :
    termwiseBifunctor F V ⟶ termwiseBifunctor F K where
  app P := ((F.obj P).mapHomologicalComplex (.up ℤ)).map p
  naturality _ _ g :=
    ((NatTrans.mapHomologicalComplex (F.map g) (.up ℤ)).naturality p).symm

private theorem fixed_comparison_iso
    {C : Type*} [Category* C] {B : Type*} [Category* B]
    {D : Type*} [Category* D]
    {F : C ⥤ B} {S : C ⥤ B} {T : B ⥤ B} (Q : B ⥤ D)
    {H H' : D ⥤ D} (a : F ≅ S ⋙ T) (c : T ⋙ Q ≅ Q ⋙ H) (d : H ≅ H') :
    Nonempty (F ⋙ Q ≅ (S ⋙ Q) ⋙ H') :=
  ⟨Functor.isoWhiskerRight a Q ≪≫ Functor.isoWhiskerLeft S c ≪≫
    Functor.isoWhiskerLeft (S ⋙ Q) d⟩

private theorem product_family_on_cocone
    {C : Type*} [Category* C] {B : Type*} [Category* B] {D : Type*} [Category* D]
    {I : Type*} [Category* I] {F : I ⥤ C} (c : Cocone F)
    (T : C ⥤ B) (Q : B ⥤ D) (S : C ⥤ D) (V : D × D ⥤ D) (A : D)
    (P : C → Prop) (hF : ∀ i, P (F.obj i)) (hc : P c.pt)
    (h : ∃ e : ∀ X, P X → (Q.obj (T.obj X) ≅ V.obj (S.obj X, A)),
      ∀ X Y (hX : P X) (hY : P Y) (g : X ⟶ Y),
        Q.map (T.map g) ≫ (e Y hY).hom =
          (e X hX).hom ≫ V.map (S.map g, 𝟙 A)) :
    ∃ (e : ∀ i, Q.obj (T.obj (F.obj i)) ≅ V.obj (S.obj (F.obj i), A))
      (b : Q.obj (T.obj c.pt) ≅ V.obj (S.obj c.pt, A)),
      (∀ i j (g : i ⟶ j), Q.map (T.map (F.map g)) ≫ (e j).hom =
        (e i).hom ≫ V.map (S.map (F.map g), 𝟙 A)) ∧
      (∀ i, Q.map (T.map (c.ι.app i)) ≫ b.hom =
        (e i).hom ≫ V.map (S.map (c.ι.app i), 𝟙 A)) := by
  obtain ⟨e, he⟩ := h
  exact ⟨fun i ↦ e _ (hF i), e _ hc,
    fun i j g ↦ he _ _ (hF i) (hF j) _, fun i ↦ he _ _ (hF i) hc _⟩

private theorem family_from_fixed_comparison
    {M D : Type*} [Category* M] [Preadditive M] [HasZeroObject M] [Category* D]
    (F : M ⥤ M ⥤ M) [F.PreservesZeroMorphisms]
    [∀ P, (F.obj P).PreservesZeroMorphisms]
    [∀ V K : CochainComplex M ℤ, CochainComplex.HasMapBifunctor V K F]
    (Q : CochainComplex M ℤ ⥤ D) (B : D × D ⥤ D) (A : D)
    (V K : CochainComplex M ℤ) (p : V ⟶ K) (eV : Q.obj V ≅ A)
    (c : F.map₂CochainComplex.flip.obj V ⋙ Q ≅
      Q ⋙ (Functor.curry.obj B).flip.obj (Q.obj V))
    (P : M → Prop)
    (hq : ∀ X, P X → IsIso (Q.map (((F.obj X).mapHomologicalComplex (.up ℤ)).map p))) :
    ∃ e : ∀ X, P X → (Q.obj ((termwiseBifunctor F K).obj X) ≅
        B.obj ((CochainComplex.singleFunctor M 0 ⋙ Q).obj X, A)),
      ∀ X Y hX hY (g : X ⟶ Y),
        Q.map ((termwiseBifunctor F K).map g) ≫ (e Y hY).hom =
          (e X hX).hom ≫ B.map ((CochainComplex.singleFunctor M 0 ⋙ Q).map g, 𝟙 A) := by
  let a := collapse_natIso F V
  obtain ⟨dN⟩ := fixed_comparison_iso Q a c ((Functor.curry.obj B).flip.mapIso eV)
  let t := Functor.whiskerRight (termwise_map F p) Q
  have hh : ∀ X, P X → IsIso (t.app X) := hq
  exact iso_family_of_trans t dN P hh

set_option backward.isDefEq.respectTransparency false in
private theorem site_tensor_family
    {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{u₂} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u₂})
    [HasDerivedCategory.{u₃} (SheafOfModules.KFlatFixedTensor.Modules R)]
    (A : DerivedCategory (SheafOfModules.KFlatFixedTensor.Modules R))
    (K : CochainComplex (SheafOfModules.KFlatFixedTensor.Modules R) ℤ)
    (eK : DerivedCategory.Q.{u₃}.obj K ≅ A) :
    ∃ e : ∀ P : SheafOfModules.KFlatFixedTensor.Modules R,
      SheafOfModules.IsFlatOnSite (J := J) (R := R) P →
      (DerivedCategory.Q.{u₃}.obj ((termwiseBifunctor
        (curriedTensor (SheafOfModules.KFlatFixedTensor.Modules R)) K).obj P) ≅
        (SheafOfModules.siteDerivedTensorIndependentCoefficients J R).obj
          ((DerivedCategory.singleFunctor.{u₃} _ 0).obj P, A)),
      ∀ P P' hP hP' (g : P ⟶ P'),
        DerivedCategory.Q.{u₃}.map ((termwiseBifunctor
          (curriedTensor (SheafOfModules.KFlatFixedTensor.Modules R)) K).map g) ≫
            (e P' hP').hom =
          (e P hP).hom ≫ (SheafOfModules.siteDerivedTensorIndependentCoefficients J R).map
            ((DerivedCategory.singleFunctor.{u₃} _ 0).map g, 𝟙 A) := by
  have : J.HasSheafCompose (forget₂ CommRingCat.{u₂} RingCat.{u₂}) := inferInstance
  let : MonoidalCategory (SheafOfModules.KFlatFixedTensor.Modules R) :=
    SheafOfModules.cochainModulesMonoidal R
  let : SymmetricCategory (SheafOfModules.KFlatFixedTensor.Modules R) :=
    SheafOfModules.cochainModulesSymmetric R
  have : MonoidalPreadditive (SheafOfModules.KFlatFixedTensor.Modules R) :=
    SheafOfModules.cochainModulesPreadditive R
  let M := SheafOfModules.KFlatFixedTensor.Modules R
  classical
  let S := CochainComplex.singleFunctor M 0
  let D : DerivedCategory.{u₃} M × DerivedCategory.{u₃} M ⥤
      DerivedCategory.{u₃} M := SheafOfModules.siteDerivedTensorIndependentCoefficients J R
  obtain ⟨V, p, hv, hf, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  have := hp
  have hVflat (r : ℤ) : SheafOfModules.IsFlatOnSite
      (J := J) (R := R) (V.X r) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm (hf r)
  obtain ⟨_, hc⟩ :=
    SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated R
  obtain ⟨c, _, _⟩ := (hc V hv hVflat).2.2.2.2.1
  dsimp only [SheafOfModules.KFlatFixedTensor.totalTensor,
    SheafOfModules.KFlatFixedTensor.ordinaryTensor,
    SheafOfModules.KFlatFixedTensor.derivedTensor] at c
  let eV : DerivedCategory.Q.{u₃}.obj V ≅ A :=
    asIso (DerivedCategory.Q.{u₃}.map p) ≪≫ eK
  have hq (P : M) (hP : SheafOfModules.IsFlatOnSite
      (J := J) (R := R) P) :
      IsIso (DerivedCategory.Q.{u₃}.map
        (((tensorLeft P).mapHomologicalComplex (.up ℤ)).map p)) := by
      have : PreservesFiniteLimits (SheafOfModules.siteSheafTensorRight (A := R) P) := hP.1
      have : PreservesFiniteColimits (SheafOfModules.siteSheafTensorRight (A := R) P) := hP.2
      have : PreservesFiniteLimits (tensorLeft P) :=
        preservesFiniteLimits_of_natIso ((SheafOfModules.siteSheafTensorRightIso R P) ≪≫
          (BraidedCategory.tensorLeftIsoTensorRight P).symm)
      have : PreservesFiniteColimits (tensorLeft P) :=
        preservesFiniteColimits_of_natIso ((SheafOfModules.siteSheafTensorRightIso R P) ≪≫
          (BraidedCategory.tensorLeftIsoTensorRight P).symm)
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
        (HomologicalComplex.quasiIso_map_of_preservesHomology p (tensorLeft P))
  exact family_from_fixed_comparison (curriedTensor M) DerivedCategory.Q.{u₃}
    D A V K p eV c _ hq


set_option backward.isDefEq.respectTransparency.types true in
private theorem represents (E : FiniteIntermediateField ℓ)
    (A : DerivedCategory.{u + 1} (Modules (Profinite.continuousMapRingObj E) X))
    (K : CochainComplex (Modules (Profinite.continuousMapRingObj E) X) ℤ)
    (eK : DerivedCategory.Q.{u + 1}.obj K ≅ A)
    (hcf : CoefficientFacts X ℓ E) : Represents X ℓ E A K := by
  classical
  have hi := site_tensor_family (ring (Profinite.continuousMapRingObj E) X) A K eK
  refine ⟨tensor_colimit X ℓ E K hcf.1.some, ?_⟩
  exact product_family_on_cocone (QlbarInternalHom.coefficientCocone X ℓ E)
    (tensorComplex X ℓ E K) DerivedCategory.Q.{u + 1}
    (DerivedCategory.singleFunctor.{u + 1} _ 0) (derivedTensor X ℓ E) A
    (fun P ↦ SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
      (R := ring (Profinite.continuousMapRingObj E) X) P)
    (fun i ↦ (hcf.2.1 i).2) hcf.2.2 hi


set_option backward.isDefEq.respectTransparency false

/-- Finite coefficient tensors have a common strict lower bound and the specified
closure colimit computes derived tensor; its legs induce the cohomology isomorphism.
Source: HRS Lemma 5.3(1), proof preceding (5.4), and before Lemma 5.6
(blueprint: lem-sfb-qlbar-bounded-tensor-colimit).

Proof:
1. The tail finite-free algebra presentation gives filteredness, finite freeness
   and the module colimit with the original inclusion legs, on both X and Y.
2. A finite basis identifies tensor with a finite direct sum, hence an exact
   functor. The filtered-colimit-flat-module-sheaves lemma gives closure flatness.
3. Untwisted Cartesian coefficients give exact pullback and its coefficient
   identifications. Coefficient-change naturality identifies the inclusion legs.
4. The standard t-structure and good lower truncation supply K strictly above a.
5. Choose one flat-term K-flat resolution V to K. Flat degree-zero coefficients
   are K-flat, so site-derived-tensor-descent identifies tensor with V with the
   derived tensor. Exact tensor carries V to K quasi-isomorphically, giving the
   asserted isomorphisms for any representative. Their naturality fixes every leg.
6. Tensor preserves the coefficient colimit in every degree. Tensor with zero
   vanishes, so all stages and the vertex retain the same strict bound a.
7. The faithful exact colimit-preserving forgetful functor to abelian sheaves
   transfers exactness of filtered colimits to module sheaves (Stacks 03DB).
   Apply exact-functor-preserves-homology to the diagram complex. Its natural
   homology comparison has composites H^q(q_F tensor 1), proving the specified
   cohomology cocone is a colimit, for every unbounded representative on Y. -/
theorem bounded_tensor_colimit (E : FiniteIntermediateField ℓ)
    {Y : Scheme.{u}} (f : X ⟶ Y) :
    Nonempty (AsSmall.{u + 1} (Under E)) ∧
    IsFiltered (AsSmall.{u + 1} (Under E)) ∧
    CoefficientFacts X ℓ E ∧ CoefficientFacts Y ℓ E ∧
    exactFunctor _ _ (pullback X ℓ E f) ∧
    IsIso (condensedPullbackHom (Profinite.continuousMapRingObj E) f) ∧
    IsIso (condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f) ∧
    (∀ (F : FiniteIntermediateField ℓ) (_ : E ≤ F),
      IsIso (condensedPullbackHom (Profinite.continuousMapRingObj F) f) ∧
      (AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} f).map
          (padicSubfieldRingObjToPadicAlgCl Y ℓ F) ≫
          condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f =
        condensedPullbackHom (Profinite.continuousMapRingObj F) f ≫
          padicSubfieldRingObjToPadicAlgCl X ℓ F) ∧
    (∃ (p : QlbarInternalHom.coefficients Y ℓ E ⋙ pullback X ℓ E f ≅
          QlbarInternalHom.coefficients X ℓ E)
      (b : (pullback X ℓ E f).obj (QlbarInternalHom.coefficientCocone Y ℓ E).pt ≅
        (QlbarInternalHom.coefficientCocone X ℓ E).pt),
      ∀ i : AsSmall.{u + 1} (Under E),
        (pullback X ℓ E f).map
            ((QlbarInternalHom.coefficientCocone Y ℓ E).ι.app i) ≫ b.hom =
          p.hom.app i ≫ (QlbarInternalHom.coefficientCocone X ℓ E).ι.app i) ∧
    (∀ (a : ℤ) (C : DerivedCategory (Modules (Profinite.continuousMapRingObj E) X)),
      C.IsGE a → ∃ K : CochainComplex (Modules (Profinite.continuousMapRingObj E) X) ℤ,
        Nonempty (DerivedCategory.Q.obj K ≅ C) ∧ K.IsStrictlyGE a ∧
        Represents X ℓ E C K ∧
        (∀ i : AsSmall.{u + 1} (Under E),
          ((tensorComplex X ℓ E K).obj
            ((QlbarInternalHom.coefficients X ℓ E).obj i)).IsStrictlyGE a) ∧
        (tensorCocone X ℓ E K).pt.IsStrictlyGE a) ∧
    (∀ (A : DerivedCategory (Modules (Profinite.continuousMapRingObj E) Y))
      (J : CochainComplex (Modules (Profinite.continuousMapRingObj E) Y) ℤ),
      Nonempty (DerivedCategory.Q.obj J ≅ A) → Represents Y ℓ E A J ∧
        ∀ q : ℤ, Nonempty (IsColimit
          ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor _ q).mapCocone
            (tensorCocone Y ℓ E J)))) := by
  classical
  have hI : IsFiltered (AsSmall.{u + 1} (Under E)) :=
    (QlbarInternalHom.fieldDiagram.{u, u} X ℓ E).1
  have hX : CoefficientFacts X ℓ E := coefficient_facts X ℓ E
  have hY : CoefficientFacts Y ℓ E := coefficient_facts Y ℓ E
  have hexact : exactFunctor _ _ (pullback X ℓ E f) := by
    change PreservesFiniteLimits (pullback X ℓ E f) ∧
      PreservesFiniteColimits (pullback X ℓ E f)
    exact ⟨inferInstance, inferInstance⟩
  have hpull := pullback_coefficients X ℓ E f hX.1 hY.1
  refine ⟨⟨(AsSmall.equiv (C := Under E)).functor.obj (Under.mk (𝟙 E))⟩,
    hI, hX, hY, hexact, inferInstance, inferInstance, ?_, hpull, ?_, ?_⟩
  · intro F _
    exact ⟨inferInstance, map_coefficientMap_comp_condensedPullbackHom
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) f⟩
  · intro a C hC
    have := hC
    have hex : ∃ (K : CochainComplex (Modules (Profinite.continuousMapRingObj E) X) ℤ)
        (_ : K.IsStrictlyGE a), Nonempty (C ≅ DerivedCategory.Q.{u + 1}.obj K) :=
      DerivedCategory.exists_iso_Q_obj_of_isGE.{u + 1} C a
    obtain ⟨K, hK, ⟨eK⟩⟩ := hex
    have := hK
    exact ⟨K, ⟨eK.symm⟩, hK, represents X ℓ E C K eK.symm hX,
      fun i ↦ tensor_strict X ℓ E K a _, tensor_strict X ℓ E K a _⟩
  · intro A J hJ
    have hrep := represents Y ℓ E A J hJ.some hY
    exact ⟨hrep, tensor_homology_colimit Y ℓ E J hrep.1⟩

end AlgebraicGeometry.ProEtale.QlbarBoundedTensor
