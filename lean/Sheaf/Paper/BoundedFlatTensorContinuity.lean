/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q143
-/
module

public import Sheaf.Paper.ModuleRingedToposDerivedComparison
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Sheaf.Algebra.Homology.FlatSingleDerivedNormalization
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits
import Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares

/-! # Strict bounded flat tensor presentations and direct-image continuity

Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), comparison (5.4), page 14;
blueprint rational proper base change, paragraph (1)
(blueprint: lem-sfb-bounded-flat-tensor-continuity).

All colimits below are in module sheaves or their cochain complexes. The fixed
section-module equivalence identifies these with the ordinary internal-module
constructions. No triangulated-category colimit is asserted.
-/

@[expose] public noncomputable section

set_option autoImplicit false
-- Advisory linting of the unchanged large signatures dominates compilation time.
set_option linter.all false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u b a vB vA w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.ProEtale.ModuleRingedComparison

namespace AlgebraicGeometry.ProEtale.BoundedFlatTensorContinuity

-- The API uses this fixed coefficient map, never its large chosen construction.
attribute [local irreducible] InternalModuleOperations.coefficientMap

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ Z)]

/-- Signed sum-total tensor with a degree-zero coefficient, with its actual tensor maps.
Source: HRS Lemma 5.3(1), strict flat tensor specialization
(blueprint: lem-sfb-bounded-flat-tensor-continuity). -/
def tensorWith (Z : Scheme.{u}) (K : CochainComplex (modules Λ Z) ℤ) :
    modules Λ Z ⥤ CochainComplex (modules Λ Z) ℤ :=
  CochainComplex.singleFunctor _ 0 ⋙ (Functor.curry.obj (totalTensor Λ Z)).obj K

/-- Derived tensor with a degree-zero coefficient, using the published derived tensor.
Source: HRS Lemma 5.3(1), strict flat tensor specialization
(blueprint: lem-sfb-bounded-flat-tensor-continuity). -/
def derivedTensorWith (Z : Scheme.{u}) (K : DerivedCategory (modules Λ Z)) :
    modules Λ Z ⥤ DerivedCategory (modules Λ Z) :=
  CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q ⋙
    (Functor.curry.obj (tensor Λ Z)).obj K

/-- The strict tensor functor on coefficients on Y, pulled back to X.
Source: HRS Lemma 5.3(1), strict flat tensor specialization
(blueprint: lem-sfb-bounded-flat-tensor-continuity). -/
def pulledTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (modules Λ X) ℤ) :
    modules Λ Y ⥤ CochainComplex (modules Λ X) ℤ :=
  pullback Λ f ⋙ tensorWith Λ X K

/-- The corresponding derived tensor K tensor Lf* of a degree-zero coefficient.
Source: HRS Lemma 5.3(1), strict flat tensor specialization
(blueprint: lem-sfb-bounded-flat-tensor-continuity). -/
def derivedPulledTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (modules Λ X)) :
    modules Λ Y ⥤ DerivedCategory (modules Λ X) :=
  CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q ⋙ derivedPullback Λ f ⋙
    (Functor.curry.obj (tensor Λ X)).obj K

/-- Representation of a whole cocone, including its specified coefficient legs.
The isomorphisms are natural for the diagram's transition maps and intertwine the
actual strict and derived tensor legs, so they form an isomorphism of cocones.
Source: HRS Lemma 5.3(1), comparison (5.4)
(blueprint: lem-sfb-bounded-flat-tensor-continuity). -/
def RepresentsCocone {B : Type b} {A : Type a} [Category.{vB} B]
    [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A] {I : Type (u + 1)} [SmallCategory I]
    {P : I ⥤ B} (c : Cocone P) (F : B ⥤ CochainComplex A ℤ)
    (D : B ⥤ DerivedCategory A) : Prop :=
  ∃ e : DerivedCategory.Q.obj (F.obj c.pt) ≅ D.obj c.pt,
    ∃ ei : ∀ i : I, DerivedCategory.Q.obj (F.obj (P.obj i)) ≅ D.obj (P.obj i),
      (∀ (i j : I) (g : i ⟶ j), DerivedCategory.Q.map (F.map (P.map g)) ≫ (ei j).hom =
        (ei i).hom ≫ D.map (P.map g)) ∧
      ∀ i : I, DerivedCategory.Q.map (F.map (c.ι.app i)) ≫ e.hom =
        (ei i).hom ≫ D.map (c.ι.app i)

/-- Apply the chosen replacement and then the actual termwise module direct image.
Source: HRS Lemma 5.3(1), comparison (5.4)
(blueprint: lem-sfb-bounded-flat-tensor-continuity). -/
def replacedPush {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : CochainComplex (modules Λ X) ℤ ⥤ CochainComplex (modules Λ X) ℤ) :
    CochainComplex (modules Λ X) ℤ ⥤ CochainComplex (modules Λ Y) ℤ :=
  J ⋙ (pushforward Λ f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The canonical K-injective computation of G, normalized by the augmentation eta.
Source: HRS Lemma 5.3(1), comparison (5.4); Stacks 070G
(blueprint: lem-sfb-bounded-flat-tensor-continuity). -/
def replacementComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : CochainComplex (modules Λ X) ℤ ⥤ CochainComplex (modules Λ X) ℤ)
    (η : 𝟭 _ ⟶ J) (hJ : ∀ M, QuasiIso (η.app M) ∧ (J.obj M).IsKInjective)
    (M : CochainComplex (modules Λ X) ℤ) :
    DerivedCategory.Q.obj ((replacedPush Λ f J).obj M) ≅
      (derivedPushforward Λ f).obj (DerivedCategory.Q.obj M) :=
  letI := (hJ M).1
  letI := (hJ M).2
  ((derivedPushforward Λ f).mapIso (asIso (DerivedCategory.Q.map (η.app M))) ≪≫
    (pushforward Λ f).rightDerivedFunctorObjQIso (J.obj M)).symm


private theorem tensorWith_preservesColimits (Z : Scheme.{u})
    (A : CochainComplex (modules Λ Z) ℤ) {I : Type (u + 1)} [SmallCategory I] :
    PreservesColimitsOfShape I (tensorWith Λ Z A) := by
  have : ∀ M : modules Λ Z, PreservesColimitsOfShape I (tensorLeft M) := fun M ↦ by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients (ring Λ Z) M
    infer_instance
  have hs : PreservesColimitsOfShape I (CochainComplex.singleFunctor (modules Λ Z) 0) := by
    change PreservesColimitsOfShape I (HomologicalComplex.single (modules Λ Z) (.up ℤ) 0)
    infer_instance
  have ht : PreservesColimitsOfShape I
      (((curriedTensor (modules Λ Z)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).obj A) := by
    infer_instance
  unfold tensorWith totalTensor
  have e : ((curriedTensor (modules Λ Z)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)).obj A ≅
      (Functor.curry.obj (cochainTotalFunctor (curriedTensor (modules Λ Z)))).obj A :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro B B' g
      simp [cochainTotalFunctor])
  exact preservesColimitsOfShape_of_natIso (Functor.isoWhiskerLeft _ e)

private theorem tensorWith_zero_below (Z : Scheme.{u})
    (A : CochainComplex (modules Λ Z) ℤ) (a : ℤ)
    (hA : ∀ n : ℤ, n < a → IsZero (A.X n)) (M : modules Λ Z)
    (n : ℤ) (hn : n < a) : IsZero (((tensorWith Λ Z A).obj M).X n) := by
  let e := (SheafOfModules.FlatSingleDerivedNormalization.collapse (ring Λ Z) M).app A
  exact (Functor.map_isZero (tensorRight M) (hA n hn)).of_iso
    ((HomologicalComplex.eval _ (.up ℤ) n).mapIso e)

open SheafOfModules.FlatSingleDerivedNormalization in
private theorem flat_single_kFlat (Z : Scheme.{u}) (M : modules Λ Z)
    (hM : exactFunctor _ _ ((curriedTensor (modules Λ Z)).obj M)) :
    CochainComplex.IsKFlatIndependentCoefficients
      ((CochainComplex.singleFunctor (modules Λ Z) 0).obj M) := by
  have hright : exactFunctor _ _ (tensorRight M) :=
    (exactFunctor _ _).prop_of_iso (BraidedCategory.tensorLeftIsoTensorRight M) hM
  let e :
      SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := ring Λ Z) M ≅
        tensorRight M :=
    SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} (ring Λ Z) M
  have hsite : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology Z) (R := ring Λ Z) M :=
    (exactFunctor (modules Λ Z) (modules Λ Z)).prop_of_iso e.symm hright
  exact (flat_single_derived_normalization.{u + 1, u, u + 1, u + 1}
    (ring Λ Z) M hsite).choose

private def tensorWith_comparison (Z : Scheme.{u})
    (A : CochainComplex (modules Λ Z) ℤ) :
    derivedTensorWith Λ Z (DerivedCategory.Q.obj A) ⟶
      tensorWith Λ Z A ⋙ DerivedCategory.Q where
  app M := (qTensor Λ Z).app (A, (CochainComplex.singleFunctor _ 0).obj M)
  naturality {M N} f := by
    have h := (qTensor Λ Z).naturality
      (Prod.mkHom (𝟙 A) ((CochainComplex.singleFunctor _ 0).map f))
    simpa [derivedTensorWith, tensorWith, Functor.curry_obj_obj_map] using h

private theorem tensorWith_comparison_app (Z : Scheme.{u})
    (A : CochainComplex (modules Λ Z) ℤ) (M : modules Λ Z) :
    (tensorWith_comparison Λ Z A).app M =
      (qTensor Λ Z).app (A, (CochainComplex.singleFunctor _ 0).obj M) := rfl

attribute [local irreducible] tensorWith_comparison

private theorem represents_of_comparison
    {B : Type b} {A : Type a} [Category.{vB} B] [Category.{vA} A]
    [Abelian A] [HasDerivedCategory.{w} A] {I : Type (u + 1)} [SmallCategory I]
    {P : I ⥤ B} (c : Cocone P) (F : B ⥤ CochainComplex A ℤ)
    (D : B ⥤ DerivedCategory A) (t : D ⟶ F ⋙ DerivedCategory.Q)
    (hc : IsIso (t.app c.pt)) (hP : ∀ i, IsIso (t.app (P.obj i))) :
    RepresentsCocone c F D := by
  have := hc
  have := hP
  refine ⟨(asIso (t.app c.pt)).symm,
    fun i ↦ (asIso (t.app (P.obj i))).symm, ?_, ?_⟩
  · intro i j g
    apply (cancel_epi (t.app (P.obj i))).mp
    change t.app (P.obj i) ≫ (F ⋙ DerivedCategory.Q).map (P.map g) ≫ _ = _
    rw [← t.naturality_assoc]
    simp
  · intro i
    apply (cancel_epi (t.app (P.obj i))).mp
    change t.app (P.obj i) ≫ (F ⋙ DerivedCategory.Q).map (c.ι.app i) ≫ _ = _
    rw [← t.naturality_assoc]
    simp

private theorem represents_precompose
    {B C : Type*} {A : Type*} [Category B] [Category C] [Category A]
    [Abelian A] [HasDerivedCategory A] {I : Type (u + 1)} [SmallCategory I]
    {P : I ⥤ B} (c : Cocone P) (G : B ⥤ C)
    (F : C ⥤ CochainComplex A ℤ) (D : C ⥤ DerivedCategory A)
    (h : RepresentsCocone (G.mapCocone c) F D) :
    RepresentsCocone c (G ⋙ F) (G ⋙ D) := h

private theorem represents_target_iso
    {B A : Type*} [Category B] [Category A] [Abelian A] [HasDerivedCategory A]
    {I : Type (u + 1)} [SmallCategory I] {P : I ⥤ B} (c : Cocone P)
    (F : B ⥤ CochainComplex A ℤ) {D D' : B ⥤ DerivedCategory A} (d : D ≅ D')
    (h : RepresentsCocone c F D) : RepresentsCocone c F D' := by
  obtain ⟨e, ei, ht, hl⟩ := h
  refine ⟨e ≪≫ d.app c.pt, (fun i ↦ ei i ≪≫ d.app (P.obj i)), ?_, ?_⟩
  · intro i j g
    dsimp only [Iso.trans_hom]
    rw [← Category.assoc, ht i j g, Category.assoc]
    simpa only [Category.assoc, Iso.app_hom, Functor.const_obj_obj] using
      congrArg (fun z ↦ (ei i).hom ≫ z) (d.hom.naturality (P.map g))
  · intro i
    dsimp only [Iso.trans_hom]
    rw [← Category.assoc, hl i, Category.assoc]
    simpa only [Category.assoc, Iso.app_hom, Functor.const_obj_obj] using
      congrArg (fun z ↦ (ei i).hom ≫ z) (d.hom.naturality (c.ι.app i))

attribute [local irreducible] RepresentsCocone

private theorem tensorWith_represents (Z : Scheme.{u})
    {I : Type (u + 1)} [SmallCategory I] {P : I ⥤ modules Λ Z} (c : Cocone P)
    (A : CochainComplex (modules Λ Z) ℤ) (K : DerivedCategory (modules Λ Z))
    (e : DerivedCategory.Q.obj A ≅ K)
    (hc : CochainComplex.IsKFlatIndependentCoefficients A ∨
      CochainComplex.IsKFlatIndependentCoefficients ((CochainComplex.singleFunctor _ 0).obj c.pt))
    (hP : ∀ i, CochainComplex.IsKFlatIndependentCoefficients A ∨
      CochainComplex.IsKFlatIndependentCoefficients
        ((CochainComplex.singleFunctor _ 0).obj (P.obj i))) :
    RepresentsCocone c (tensorWith Λ Z A) (derivedTensorWith Λ Z K) := by
  let eD : derivedTensorWith Λ Z (DerivedCategory.Q.obj A) ≅
      derivedTensorWith Λ Z K :=
    Functor.isoWhiskerLeft (CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q)
      ((Functor.curry.obj (tensor Λ Z)).mapIso e)
  let t := eD.inv ≫ tensorWith_comparison Λ Z A
  have ht (M : modules Λ Z)
      (hM : CochainComplex.IsKFlatIndependentCoefficients A ∨
        CochainComplex.IsKFlatIndependentCoefficients
          ((CochainComplex.singleFunctor _ 0).obj M)) : IsIso (t.app M) := by
    have : IsIso ((tensorWith_comparison Λ Z A).app M) := by
      rw [tensorWith_comparison_app]
      exact (tensor_representatives Λ Z).exists.choose_spec.2.1 A _ hM
    dsimp only [t, NatTrans.comp_app]
    infer_instance
  exact represents_of_comparison c _ _ t (ht c.pt hc) (fun i ↦ ht (P.obj i) (hP i))

private def single_derived_tensor_iso
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (T : DerivedCategory D ⥤ E) :
    F ⋙ (CochainComplex.singleFunctor D 0 ⋙ DerivedCategory.Q ⋙ T) ≅
      (CochainComplex.singleFunctor C 0 ⋙ DerivedCategory.Q) ⋙ F.mapDerivedCategory ⋙ T := by
  let e : F ⋙ CochainComplex.singleFunctor D 0 ⋙ DerivedCategory.Q ≅
      (CochainComplex.singleFunctor C 0 ⋙ DerivedCategory.Q) ⋙ F.mapDerivedCategory :=
    Functor.isoWhiskerRight (F.mapCochainComplexSingleFunctor 0).symm DerivedCategory.Q ≪≫
      Functor.isoWhiskerLeft (CochainComplex.singleFunctor C 0) F.mapDerivedCategoryFactors.symm
  exact (Functor.associator F (CochainComplex.singleFunctor D 0 ⋙ DerivedCategory.Q) T).symm ≪≫
    Functor.isoWhiskerRight e T ≪≫ Functor.associator _ _ _

attribute [local irreducible] single_derived_tensor_iso

private def derivedPulledTensor_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (modules Λ X)) :
    pullback Λ f ⋙ derivedTensorWith Λ X K ≅ derivedPulledTensor Λ f K := by
  exact single_derived_tensor_iso (pullback Λ f) ((Functor.curry.obj (tensor Λ X)).obj K)

attribute [local irreducible] derivedPulledTensor_iso

private theorem colimit_desc_quasiIso_of_computation
    {C D : Type*} [Category C] [Category D] [Abelian D] [HasDerivedCategory D]
    {I : Type*} [Category I] [HasColimitsOfShape I D]
    [HasExactColimitsOfShape I D]
    (F : C ⥤ CochainComplex D ℤ) (H : C ⥤ DerivedCategory D)
    (e : F ⋙ DerivedCategory.Q ≅ H) {P : I ⥤ C} (c : Cocone P)
    (hc : ∀ q : ℤ, Nonempty (IsColimit
      ((H ⋙ DerivedCategory.homologyFunctor D q).mapCocone c))) :
    QuasiIso (colimit.desc (P ⋙ F) (F.mapCocone c)) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let T := HomologicalComplex.homologyFunctor D (.up ℤ) q
  let d : F ⋙ T ≅ H ⋙ DerivedCategory.homologyFunctor D q :=
    Functor.isoWhiskerLeft F (DerivedCategory.homologyFunctorFactors D q).symm ≪≫
      Functor.isoWhiskerRight e (DerivedCategory.homologyFunctor D q)
  let htarget : IsColimit ((F ⋙ T).mapCocone c) :=
    IsColimit.mapCoconeEquiv d.symm (hc q).some
  let hsource := isColimitOfPreserves T (colimit.isColimit (P ⋙ F))
  let i := hsource.coconePointUniqueUpToIso htarget
  have hi : T.map (colimit.desc (P ⋙ F) (F.mapCocone c)) = i.hom := by
    apply hsource.hom_ext
    intro j
    change T.map (colimit.ι (P ⋙ F) j) ≫ _ = _
    rw [← T.map_comp, colimit.ι_desc]
    exact (IsColimit.comp_coconePointUniqueUpToIso_hom hsource htarget j).symm
  change IsIso (T.map (colimit.desc (P ⋙ F) (F.mapCocone c)))
  rw [hi]
  infer_instance

private def replacement_computation
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (RF : DerivedCategory C ⥤ DerivedCategory D)
    (α : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hα : ∀ M : CochainComplex C ℤ, M.IsKInjective → IsIso (α.app M))
    (J : CochainComplex C ℤ ⥤ CochainComplex C ℤ) (η : 𝟭 _ ⟶ J)
    (hJ : ∀ M, QuasiIso (η.app M) ∧ (J.obj M).IsKInjective) :
    J ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF := by
  have : ∀ M, IsIso ((Functor.whiskerLeft J α).app M) := fun M ↦ hα _ (hJ M).2
  have : IsIso (Functor.whiskerLeft J α) := NatIso.isIso_of_isIso_app _
  have : ∀ M, IsIso ((Functor.whiskerRight η DerivedCategory.Q).app M) := by
    intro M
    have := (hJ M).1
    change IsIso (DerivedCategory.Q.map (η.app M))
    infer_instance
  have : IsIso (Functor.whiskerRight η DerivedCategory.Q) := NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerLeft J α) ≪≫
    (Functor.isoWhiskerRight (asIso (Functor.whiskerRight η DerivedCategory.Q)) RF).symm

attribute [local irreducible] replacement_computation

private def isColimit_map_of_canonical
    {C D : Type*} [Category C] [Category D] {I : Type*} [Category I]
    (F : I ⥤ C) [HasColimit F] (c : Cocone F) (hc : IsColimit c) (H : C ⥤ D)
    (h : IsColimit (H.mapCocone (colimit.cocone F))) : IsColimit (H.mapCocone c) := by
  let i := (colimit.isColimit F).coconePointUniqueUpToIso hc
  refine IsColimit.ofIsoColimit h (Cocone.ext (H.mapIso i) (fun j ↦ ?_))
  change H.map (colimit.ι F j) ≫ H.map i.hom = H.map (c.ι.app j)
  rw [← H.map_comp]
  exact congrArg H.map (IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit F) hc j)

attribute [local irreducible] isColimit_map_of_canonical

private theorem cochain_right_unit_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (RF : DerivedCategory C ⥤ DerivedCategory D)
    (η : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (M : CochainComplex C ℤ)
    [IsIso (η.app ((HomotopyCategory.quotient C (.up ℤ)).obj M))] :
    IsIso ((derivedCochainRightUnit F RF η).app M) := by
  dsimp only [derivedCochainRightUnit, NatTrans.comp_app, Functor.whiskerLeft_app]
  infer_instance

private def isColimit_of_iso_desc
    {C D : Type*} [Category C] [Category D] {I : Type*} [Category I]
    (F : I ⥤ C) [HasColimit F] (H : C ⥤ D) [HasColimit (F ⋙ H)]
    [IsIso (colimit.desc (F ⋙ H) (H.mapCocone (colimit.cocone F)))] :
    IsColimit (H.mapCocone (colimit.cocone F)) := by
  have hdesc : (colimit.isColimit (F ⋙ H)).desc (H.mapCocone (colimit.cocone F)) =
      colimit.desc (F ⋙ H) (H.mapCocone (colimit.cocone F)) := by
    apply colimit.hom_ext
    intro j
    simp
  exact ((colimit.isColimit (F ⋙ H)).nonempty_isColimit_iff_isIso_desc).2
    (hdesc.symm ▸ inferInstance) |>.some

attribute [local irreducible] isColimit_of_iso_desc

private theorem bounded_ring_model {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1})
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex (SheafOfModules.{u + 1} R) ℤ) (c : Cocone D)
    (hc : IsColimit c) (a : ℤ)
    (hD : ∀ i : I, ∀ n : ℤ, n < a → IsZero ((D.obj i).X n))
    (J : CochainComplex (SheafOfModules.{u + 1} R) ℤ ⥤
      CochainComplex (SheafOfModules.{u + 1} R) ℤ)
    (η : 𝟭 _ ⟶ J) (hJ : ∀ M, QuasiIso (η.app M) ∧ (J.obj M).IsKInjective) :
    QuasiIso (colimit.desc
      (D ⋙ J ⋙ (Scheme.ProEt.ringModuleDirectImage f R).mapHomologicalComplex (.up ℤ))
      ((J ⋙ (Scheme.ProEt.ringModuleDirectImage f R).mapHomologicalComplex
        (.up ℤ)).mapCocone c)) := by
  let F := Scheme.ProEt.ringModuleDirectImage f R
  let RF := Scheme.ProEt.ringDerivedDirectImage f R
  let hres := Scheme.ProEt.ringModuleDirectImage_hasKInjectiveResolutions R
  let α := derivedCochainRightUnit F RF (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit hres)
  have hα (M : CochainComplex (SheafOfModules.{u + 1} R) ℤ) (hM : M.IsKInjective) :
      IsIso (α.app M) := by
    have := hM
    have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso hres M
    exact cochain_right_unit_isIso F RF _ M
  have e := replacement_computation F RF α hα J η hJ
  let S := (Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).obj R
  have : ReflectsFiniteLimits (SheafOfModules.toSheaf.{u + 1} S) :=
    reflectsFiniteLimits_of_reflectsIsomorphisms _
  have : PreservesColimitsOfShape I (SheafOfModules.toSheaf.{u + 1} S) :=
    (moduleSheaves_colimits_forgetful S).2.2.2.2.2 I |>.2.1
  have : HasExactColimitsOfShape I (SheafOfModules.{u + 1} S) :=
    HasExactColimitsOfShape.domain_of_functor I (SheafOfModules.toSheaf S)
  apply colimit_desc_quasiIso_of_computation _ _ e c
  intro q
  let H := DerivedCategory.Q ⋙ Scheme.ProEt.ringHigherDirectImage f R q
  have : IsIso (colimit.desc (D ⋙ H) (H.mapCocone (colimit.cocone D))) :=
    Scheme.ProEt.boundedContinuityDirectImage f R D a hD q
  exact ⟨isColimit_map_of_canonical D c hc H (isColimit_of_iso_desc D H)⟩

private def ring_push_scalar_iso
    {C D : Type*} [Category C] [Category D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K]
    (R : Sheaf K RingCat.{u + 1}) (S : Sheaf J RingCat.{u + 1})
    (α : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R) :
    SheafOfModules.pushforward.{u + 1} (F := F) (𝟙 _ :
        (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R ⟶ _) ⋙
        SheafOfModules.restrictScalars.{u + 1} α ≅
      SheafOfModules.pushforward.{u + 1} (F := F) α :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget S).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        (ModuleCat.restrictScalars (α.hom.app U).hom).mapIso
          (ModuleCat.restrictScalarsId'App _ rfl (M.val.obj (F.op.obj U))))
        (by intros; ext x; rfl)))
    (by intros; apply SheafOfModules.hom_ext; apply PresheafOfModules.hom_ext; intro U; ext x; rfl)

attribute [local irreducible] ring_push_scalar_iso

private theorem colimit_desc_post
    {C D E : Type*} [Category C] [Category D] [Category E]
    {I : Type*} [Category I] [HasColimitsOfShape I D] [HasColimitsOfShape I E]
    (P : I ⥤ C) (c : Cocone P) (B : C ⥤ D) (T : D ⥤ E) :
    colimit.desc (P ⋙ B ⋙ T) ((B ⋙ T).mapCocone c) =
      colimit.post (P ⋙ B) T ≫ T.map (colimit.desc (P ⋙ B) (B.mapCocone c)) := by
  exact (colimit.post_desc (P ⋙ B) T (B.mapCocone c)).symm

private theorem colimit_desc_congr
    {C D : Type*} [Category C] [Category D]
    {I : Type*} [Category I] [HasColimitsOfShape I D]
    {P : I ⥤ C} (c : Cocone P) {F G : C ⥤ D} (e : F ≅ G) :
    (colim.mapIso (Functor.isoWhiskerLeft P e)).hom ≫
        colimit.desc (P ⋙ G) (G.mapCocone c) =
      colimit.desc (P ⋙ F) (F.mapCocone c) ≫ (e.app c.pt).hom := by
  apply colimit.hom_ext
  intro i
  simp only [Functor.mapIso_hom, colimit.ι_map_assoc,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    colimit.ι_desc, colimit.ι_desc_assoc]
  simpa only [Functor.mapCocone_ι_app, Iso.app_hom,
    Functor.comp_obj, Functor.const_obj_obj, Functor.mapCocone_pt] using
    (e.hom.naturality (c.ι.app i)).symm

private theorem scalar_restriction_properties (Y : Scheme.{u})
    (R S : Sheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}) (α : R ⟶ S)
    {I : Type (u + 1)} [SmallCategory I] :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u + 1} α) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{u + 1} α) ∧
      PreservesColimitsOfShape I (SheafOfModules.restrictScalars.{u + 1} α) := by
  let U := SheafOfModules.toSheaf.{u + 1} R
  let V := SheafOfModules.toSheaf.{u + 1} S
  let T := SheafOfModules.restrictScalars.{u + 1} α
  have : PreservesFiniteColimits U := (moduleSheaves_colimits_forgetful R).2.2.1
  have : PreservesFiniteColimits V := (moduleSheaves_colimits_forgetful S).2.2.1
  have : PreservesColimitsOfShape I U :=
    (moduleSheaves_colimits_forgetful R).2.2.2.2.2 I |>.2.1
  have : PreservesColimitsOfShape I V :=
    (moduleSheaves_colimits_forgetful S).2.2.2.2.2 I |>.2.1
  have : ReflectsFiniteLimits U := reflectsFiniteLimits_of_reflectsIsomorphisms U
  have : ReflectsFiniteColimits U := reflectsFiniteColimitsOfReflectsIsomorphisms U
  have : ReflectsColimitsOfShape I U := reflectsColimitsOfShape_of_reflectsIsomorphisms
  have : PreservesFiniteLimits (T ⋙ U) := inferInstanceAs (PreservesFiniteLimits V)
  have : PreservesFiniteColimits (T ⋙ U) := inferInstanceAs (PreservesFiniteColimits V)
  have : PreservesColimitsOfShape I (T ⋙ U) := inferInstanceAs (PreservesColimitsOfShape I V)
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves T U,
    preservesFiniteColimits_of_reflects_of_preserves T U,
    preservesColimitsOfShape_of_reflects_of_preserves T U⟩

omit [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ Z)] in
private theorem bounded_push_model {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex (modules Λ X) ℤ) (c : Cocone D) (hc : IsColimit c)
    (a : ℤ) (hD : ∀ i : I, ∀ n : ℤ, n < a → IsZero ((D.obj i).X n))
    (J : CochainComplex (modules Λ X) ℤ ⥤ CochainComplex (modules Λ X) ℤ)
    (η : 𝟭 _ ⟶ J) (hJ : ∀ M, QuasiIso (η.app M) ∧ (J.obj M).IsKInjective) :
    QuasiIso (colimit.desc (D ⋙ replacedPush Λ f J) ((replacedPush Λ f J).mapCocone c)) := by
  let R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} :=
    (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring Λ X)
  let S := (Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).obj R
  let T := SheafOfModules.restrictScalars.{u + 1} (coefficientMap Λ f)
  have hp := scalar_restriction_properties Y _ S (coefficientMap Λ f) (I := I)
  have : PreservesFiniteLimits T := hp.1
  have : PreservesFiniteColimits T := hp.2.1
  have : PreservesColimitsOfShape I T := hp.2.2
  let F := Scheme.ProEt.ringModuleDirectImage f R
  let B := J ⋙ F.mapHomologicalComplex (.up ℤ)
  let Tc := T.mapHomologicalComplex (.up ℤ)
  have hq : QuasiIso (colimit.desc (D ⋙ B) (B.mapCocone c)) :=
    bounded_ring_model f R D c hc a hD J η hJ
  have : QuasiIso (Tc.map (colimit.desc (D ⋙ B) (B.mapCocone c))) := by
    have := hq
    infer_instance
  have hq' : QuasiIso (colimit.desc (D ⋙ B ⋙ Tc) ((B ⋙ Tc).mapCocone c)) := by
    rw [colimit_desc_post]
    infer_instance
  have eF : F ⋙ T ≅ pushforward Λ f :=
    ring_push_scalar_iso (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
      (Scheme.proEtaleBaseChange f) R _ (coefficientMap Λ f)
  have e : B ⋙ Tc ≅ replacedPush Λ f J :=
    Functor.isoWhiskerLeft J (Functor.mapHomologicalComplexCompIso eF (.up ℤ))
  let ei := colim.mapIso (Functor.isoWhiskerLeft D e)
  have he' := colimit_desc_congr c e
  exact ((HomologicalComplex.quasiIso (modules Λ Y) (.up ℤ)).arrow_mk_iso_iff
    (Arrow.isoMk ei (e.app c.pt) he')).1 hq'

private theorem localized_quotient_map
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {M N : CochainComplex C ℤ} (g : M ⟶ N) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map g) =
      DerivedCategory.Q.map g := by
  have h := DerivedCategory.quotientCompQhIso_hom_naturality g
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _ at h
  simpa only [Category.comp_id, Category.id_comp] using h

private theorem right_comparison_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] {M N : CochainComplex C ℤ}
    [M.IsKInjective] [N.IsKInjective] (g : M ⟶ N) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map g) ≫
        (F.rightDerivedFunctorObjQIso N).inv =
      (F.rightDerivedFunctorObjQIso M).inv ≫
        F.rightDerivedFunctor.map (DerivedCategory.Q.map g) := by
  have h := F.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient C (.up ℤ)).map g)
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_inv,
    Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv, asIso_hom, Iso.app_hom]
  change _ ≫ ((𝟙 _ ≫ _) ≫ F.rightDerivedFunctor.map (𝟙 _)) =
    ((𝟙 _ ≫ _) ≫ F.rightDerivedFunctor.map (𝟙 _)) ≫ _
  simp only [Category.id_comp]
  erw [F.rightDerivedFunctor.map_id, F.rightDerivedFunctor.map_id]
  simp only [Category.comp_id]
  simpa only [Functor.comp_map, Functor.mapHomotopyCategory_map,
    localized_quotient_map] using h

private theorem replacement_comparison_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : CochainComplex (modules Λ X) ℤ ⥤ CochainComplex (modules Λ X) ℤ)
    (η : 𝟭 _ ⟶ J) (hJ : ∀ M, QuasiIso (η.app M) ∧ (J.obj M).IsKInjective)
    {M N : CochainComplex (modules Λ X) ℤ} (g : M ⟶ N) :
    DerivedCategory.Q.map ((replacedPush Λ f J).map g) ≫
        (replacementComparison Λ f J η hJ N).hom =
      (replacementComparison Λ f J η hJ M).hom ≫
        (derivedPushforward Λ f).map (DerivedCategory.Q.map g) := by
  have := (hJ M).1
  have := (hJ M).2
  have := (hJ N).1
  have := (hJ N).2
  have h := right_comparison_naturality (pushforward Λ f) (J.map g)
  dsimp only [replacementComparison, Iso.symm_hom, Iso.trans_inv,
    Functor.mapIso_inv, asIso_inv, replacedPush, Functor.comp_map, derivedPushforward]
  rw [← Category.assoc, h]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 1
  apply congrArg (pushforward Λ f).rightDerivedFunctor.map
  have he : η.app M ≫ J.map g = g ≫ η.app N := (η.naturality g).symm
  have heQ := congrArg DerivedCategory.Q.map he
  simp only [Functor.map_comp] at heQ
  apply (cancel_epi (DerivedCategory.Q.map (η.app M))).mp
  simp only [IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, heQ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem localized_desc_postcompose
    {C D : Type*} [Category C] [Category D] [Abelian D] [HasDerivedCategory D]
    {I : Type*} [Category I] [HasColimitsOfShape I D]
    {B : Type*} [Category B] (P : I ⥤ B) (T : B ⥤ C)
    (F : C ⥤ CochainComplex D ℤ) (c : Cocone P)
    (h : QuasiIso (colimit.desc ((P ⋙ T) ⋙ F) (F.mapCocone (T.mapCocone c)))) :
    IsIso (DerivedCategory.Q.map
      (colimit.desc (P ⋙ T ⋙ F) (F.mapCocone (T.mapCocone c)))) := by
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso D _).2
  simpa only [Functor.assoc] using h

private theorem localized_desc_leg
    {B C D : Type*} [Category B] [Category C] [Category D] [Abelian D]
    [HasDerivedCategory D] {I : Type*} [Category I] [HasColimitsOfShape I D]
    (P : I ⥤ B) (T : B ⥤ C) (F : C ⥤ CochainComplex D ℤ) (c : Cocone P)
    (i : I) {Z : DerivedCategory D}
    (g : DerivedCategory.Q.obj (F.obj (T.obj c.pt)) ⟶ Z) :
    DerivedCategory.Q.map (colimit.ι (P ⋙ T ⋙ F) i) ≫
        DerivedCategory.Q.map (colimit.desc (P ⋙ T ⋙ F)
          (F.mapCocone (T.mapCocone c))) ≫ g =
      DerivedCategory.Q.map (F.map (T.map (c.ι.app i))) ≫ g := by
  rw [← DerivedCategory.Q.map_comp_assoc, colimit.ι_desc]
  rfl

private theorem pulledTensor_preservesColimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Kc : CochainComplex (modules Λ X) ℤ) {I : Type (u + 1)} [SmallCategory I] :
    PreservesColimitsOfShape I (pulledTensor Λ f Kc) := by
  have := tensorWith_preservesColimits Λ X Kc (I := I)
  unfold pulledTensor
  infer_instance

private theorem pulledTensor_zero_below {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Kc : CochainComplex (modules Λ X) ℤ) (a : ℤ)
    (h : ∀ n : ℤ, n < a → IsZero (Kc.X n)) (M : modules Λ Y)
    (n : ℤ) (hn : n < a) : IsZero (((pulledTensor Λ f Kc).obj M).X n) :=
  tensorWith_zero_below Λ X Kc a h ((pullback Λ f).obj M) n hn

private theorem pulledTensor_represents {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type (u + 1)} [SmallCategory I] {P : I ⥤ modules Λ Y} (c : Cocone P)
    (Kc : CochainComplex (modules Λ X) ℤ) (K : DerivedCategory (modules Λ X))
    (eK : DerivedCategory.Q.obj Kc ≅ K)
    (hC : exactFunctor _ _ ((curriedTensor (modules Λ X)).obj ((pullback Λ f).obj c.pt)))
    (hP : ∀ i, exactFunctor _ _
      ((curriedTensor (modules Λ X)).obj ((pullback Λ f).obj (P.obj i)))) :
    RepresentsCocone c (pulledTensor Λ f Kc) (derivedPulledTensor Λ f K) := by
  have hr := tensorWith_represents Λ X ((pullback Λ f).mapCocone c) Kc K eK
    (Or.inr (flat_single_kFlat Λ X _ hC))
    (fun i ↦ Or.inr (flat_single_kFlat Λ X _ (hP i)))
  exact represents_target_iso c _ (derivedPulledTensor_iso Λ f K)
    (represents_precompose c (pullback Λ f) _ _ hr)

attribute [local irreducible] replacementComparison replacedPush
  tensorWith derivedTensorWith pulledTensor derivedPulledTensor


open SheafOfModules in
/-- Strict flat tensor colimits, K-flat models of GK, and qcqs continuity for every
functorial K-injective replacement, with the actual localized tensor cocone legs.
Source: HRS Lemma 5.3(1), proof of (5.4), page 14; rational proper base change (1)
(blueprint: lem-sfb-bounded-flat-tensor-continuity).

Proof plan:
1. Use lem-pd-module-ringed-topos-derived-comparison to pass to the section-ring
   realization, preserving the exact tensor, resolutions and specified adjunction.
2. Apply the ordinary pullback/pushforward adjunction to the unique factorization
   property of c. It gives the pulled-back colimit with legs f*(v_i).
3. Apply lem-pur-flat-single-derived-normalization to each pulled-back coefficient.
   Only the summand (r,0) survives, so all strict tensors vanish below a.
   The flat degree-zero coefficients are K-flat. The published qTensor comparison
   is invertible when either input is K-flat and natural in both inputs. Its
   inverse, followed by the specified Q(Kc) ≅ K, identifies every transition
   and leg. The exact pullback factorization identifies LP_i and LC naturally.
4. Apply lem-weil-pbc-independent-sheaf-tensor-colimits degreewise to K^r.
   The maps commute with differentials; this is the asserted strict tensor cocone
   and every evaluation cocone is a colimit.
5. Resolve a representative of GK by lem-pc-kflat-resolution. For every such A,
   tensor preserves c degreewise, without a bound on A. The same qTensor
   comparison, now invertible because A is K-flat, identifies its localized
   diagram and its actual legs with the derived tensors.
6. prop-pur-kinjective-resolutions-exist supplies J and eta. The canonical
   replacementComparison computes G, naturally on the strict tensor cocone.
7. By src-weil-homology-preserves-exact-colimits and Grothendieck abelianness,
   H^q of the colimit of f*J(E_i) is colim H^q(f*J(E_i)). Apply
   det-pe-bounded-continuity-direct-image to the uniformly bounded strict E_i,
   not to J(E_i). lem-weil-pbc-module-sheaves-colimits-forgetful detects the
   resulting R_Y-linear isomorphisms. Thus the actual colimit.desc is a
   quasi-isomorphism, and its localization is invertible. The last displayed
   equation records its composite with each leg under the normalized comparisons.
8. For replacement independence use the natural zigzag J -> JJ' <- J' of
   quasi-isomorphisms between K-injectives. The K-injective Hom theorem makes
   these homotopy equivalences; additive direct image preserves them. Exact
   filtered colimits preserve their quasi-isomorphisms. The separate
   replacement_independence statement records these very maps and their square.
-/
theorem bounded_flat_tensor_continuity
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (_hp : 0 < p) (_hne : p ≠ ℓ)
    {X Y : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [QuasiCompact f.left] [QuasiSeparated f.left]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (P : I ⥤ modules Λ Y.left) (c : Cocone P) (_hc : IsColimit c)
    (_hP : ∀ i : I, exactFunctor _ _
      ((curriedTensor (modules Λ Y.left)).obj (P.obj i)))
    (_hC : exactFunctor _ _ ((curriedTensor (modules Λ Y.left)).obj c.pt))
    (_hfP : ∀ i : I, exactFunctor _ _ ((curriedTensor (modules Λ X.left)).obj
      ((pullback Λ f.left).obj (P.obj i))))
    (_hfC : exactFunctor _ _ ((curriedTensor (modules Λ X.left)).obj
      ((pullback Λ f.left).obj c.pt)))
    (K : DerivedCategory (modules Λ X.left))
    (Kc : CochainComplex (modules Λ X.left) ℤ) (_eK : DerivedCategory.Q.obj Kc ≅ K)
    (a : ℤ) (_hK : ∀ n : ℤ, n < a → IsZero (Kc.X n)) :
    Nonempty (IsColimit ((pullback Λ f.left).mapCocone c)) ∧
    (∀ i : I, ∀ n : ℤ, n < a →
      IsZero (((pulledTensor Λ f.left Kc).obj (P.obj i)).X n)) ∧
    (∀ n : ℤ, n < a → IsZero (((pulledTensor Λ f.left Kc).obj c.pt).X n)) ∧
    Nonempty (IsColimit ((pulledTensor Λ f.left Kc).mapCocone c)) ∧
    (∀ n : ℤ, Nonempty (IsColimit
      ((HomologicalComplex.eval (modules Λ X.left) (ComplexShape.up ℤ) n).mapCocone
        ((pulledTensor Λ f.left Kc).mapCocone c)))) ∧
    (∃ A : CochainComplex (modules Λ Y.left) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ Y.left) A ∧
      (∀ n : ℤ, exactFunctor _ _ ((curriedTensor (modules Λ Y.left)).obj (A.X n))) ∧
      Nonempty (DerivedCategory.Q.obj A ≅ (derivedPushforward Λ f.left).obj K)) ∧
    (∀ (A : CochainComplex (modules Λ Y.left) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ Y.left) A →
      (∀ n : ℤ, exactFunctor _ _ ((curriedTensor (modules Λ Y.left)).obj (A.X n))) →
      ∀ _eA : DerivedCategory.Q.obj A ≅ (derivedPushforward Λ f.left).obj K,
        Nonempty (IsColimit ((tensorWith Λ Y.left A).mapCocone c)) ∧
        IsIso (colimit.desc (P ⋙ tensorWith Λ Y.left A)
          ((tensorWith Λ Y.left A).mapCocone c)) ∧
        RepresentsCocone c (tensorWith Λ Y.left A)
          (derivedTensorWith Λ Y.left ((derivedPushforward Λ f.left).obj K))) ∧
    (∃ (J : CochainComplex (modules Λ X.left) ℤ ⥤
          CochainComplex (modules Λ X.left) ℤ) (η : 𝟭 _ ⟶ J),
      ∀ M, QuasiIso (η.app M) ∧ (J.obj M).IsKInjective) ∧
    (∃ e : DerivedCategory.Q.obj ((pulledTensor Λ f.left Kc).obj c.pt) ≅
          (derivedPulledTensor Λ f.left K).obj c.pt,
      ∃ ei : ∀ i : I,
          DerivedCategory.Q.obj ((pulledTensor Λ f.left Kc).obj (P.obj i)) ≅
            (derivedPulledTensor Λ f.left K).obj (P.obj i),
        (∀ (i j : I) (g : i ⟶ j),
          DerivedCategory.Q.map ((pulledTensor Λ f.left Kc).map (P.map g)) ≫ (ei j).hom =
            (ei i).hom ≫ (derivedPulledTensor Λ f.left K).map (P.map g)) ∧
        (∀ i : I,
          DerivedCategory.Q.map ((pulledTensor Λ f.left Kc).map (c.ι.app i)) ≫ e.hom =
            (ei i).hom ≫ (derivedPulledTensor Λ f.left K).map (c.ι.app i)) ∧
        ∀ (J : CochainComplex (modules Λ X.left) ℤ ⥤
            CochainComplex (modules Λ X.left) ℤ) (η : 𝟭 _ ⟶ J)
          (hJ : ∀ M, QuasiIso (η.app M) ∧ (J.obj M).IsKInjective),
          IsIso (DerivedCategory.Q.map
            (colimit.desc (P ⋙ pulledTensor Λ f.left Kc ⋙ replacedPush Λ f.left J)
              ((replacedPush Λ f.left J).mapCocone
                ((pulledTensor Λ f.left Kc).mapCocone c)))) ∧
          ∀ i : I,
            DerivedCategory.Q.map
                (colimit.ι (P ⋙ pulledTensor Λ f.left Kc ⋙ replacedPush Λ f.left J) i) ≫
              DerivedCategory.Q.map
                (colimit.desc (P ⋙ pulledTensor Λ f.left Kc ⋙ replacedPush Λ f.left J)
                  ((replacedPush Λ f.left J).mapCocone
                    ((pulledTensor Λ f.left Kc).mapCocone c))) ≫
              (replacementComparison Λ f.left J η hJ
                ((pulledTensor Λ f.left Kc).obj c.pt)).hom ≫
              (derivedPushforward Λ f.left).map e.hom =
            (replacementComparison Λ f.left J η hJ
                ((pulledTensor Λ f.left Kc).obj (P.obj i))).hom ≫
              (derivedPushforward Λ f.left).map (ei i).hom ≫
              (derivedPushforward Λ f.left).map
                ((derivedPulledTensor Λ f.left K).map (c.ι.app i))) := by
  have hpull : IsColimit ((pullback Λ f.left).mapCocone c) :=
    isColimitOfPreserves (pullback Λ f.left) _hc
  have := pulledTensor_preservesColimits Λ f.left Kc (I := I)
  have hcTensor : IsColimit ((pulledTensor Λ f.left Kc).mapCocone c) :=
    isColimitOfPreserves (pulledTensor Λ f.left Kc) _hc
  have hbound (M : modules Λ Y.left) (n : ℤ) (hn : n < a) :
      IsZero (((pulledTensor Λ f.left Kc).obj M).X n) :=
    pulledTensor_zero_below Λ f.left Kc a _hK M n hn
  refine ⟨⟨hpull⟩, (fun i n hn ↦ hbound (P.obj i) n hn), hbound c.pt,
    ⟨hcTensor⟩, (fun n ↦ ⟨isColimitOfPreserves
      (HomologicalComplex.eval _ (.up ℤ) n) hcTensor⟩), ?_, ?_, ?_, ?_⟩
  · let G := (derivedPushforward Λ f.left).obj K
    obtain ⟨A, q, hA, hAf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := ring Λ Y.left) (DerivedCategory.Q.objPreimage G)
    have := hq
    refine ⟨A, hA, ?_, ⟨asIso (DerivedCategory.Q.map q) ≪≫
      DerivedCategory.Q.objObjPreimageIso G⟩⟩
    intro n
    exact (exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight (A.X n)).symm (hAf n)
  · intro A hA _hAf eA
    have := tensorWith_preservesColimits Λ Y.left A (I := I)
    let hcA := isColimitOfPreserves (tensorWith Λ Y.left A) _hc
    refine ⟨⟨hcA⟩, ?_, tensorWith_represents Λ Y.left c A _ eA
      (Or.inl hA) (fun _ ↦ Or.inl hA)⟩
    exact hcA.coconePointUniqueUpToIso (colimit.isColimit _) |>.isIso_inv
  · obtain ⟨J, η, hJ⟩ :=
      (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X.left) (ring Λ X.left)).2.2
    exact ⟨J, η, fun M ↦ ⟨(hJ M).1, (hJ M).2.1⟩⟩
  · have hr' := pulledTensor_represents Λ f.left c Kc K _eK _hfC _hfP
    unfold RepresentsCocone at hr'
    obtain ⟨e', ei', htr', hleg'⟩ := hr'
    refine ⟨e', ei', htr', hleg', ?_⟩
    intro J η hJ
    have hq := bounded_push_model Λ f.left (P ⋙ pulledTensor Λ f.left Kc)
      ((pulledTensor Λ f.left Kc).mapCocone c) hcTensor a
      (fun i n hn ↦ hbound (P.obj i) n hn) J η hJ
    refine ⟨localized_desc_postcompose P (pulledTensor Λ f.left Kc)
      (replacedPush Λ f.left J) c hq, ?_⟩
    intro i
    rw [localized_desc_leg P (pulledTensor Λ f.left Kc) (replacedPush Λ f.left J)]
    have hn := replacement_comparison_naturality Λ f.left J η hJ
      ((pulledTensor Λ f.left Kc).map (c.ι.app i))
    simp only [Functor.const_obj_obj] at hn
    rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
      hleg' i, Functor.map_comp]


attribute [local semireducible] replacedPush tensorWith derivedTensorWith
  pulledTensor derivedPulledTensor

/-- Direct-image maps induced by a natural map of replacement functors.
Source: HRS Lemma 5.3(1), replacement independence in the strict specialization
(blueprint: lem-sfb-bounded-flat-tensor-continuity). -/
def replacementMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    {J J' : CochainComplex (modules Λ X) ℤ ⥤ CochainComplex (modules Λ X) ℤ}
    (θ : J ⟶ J') : replacedPush Λ f J ⟶ replacedPush Λ f J' :=
  Functor.whiskerRight θ ((pushforward Λ f).mapHomologicalComplex (ComplexShape.up ℤ))

/-- The concrete replacement map identifies sources, normalized targets, and the
comparison arrows. In particular the square includes every actual colimit leg.
Source: HRS Lemma 5.3(1), comparison (5.4)
(blueprint: lem-sfb-bounded-flat-tensor-continuity). -/
def ReplacementCompatible {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type (u + 1)} [SmallCategory I]
    {D : I ⥤ CochainComplex (modules Λ X) ℤ} (c : Cocone D)
    (J : CochainComplex (modules Λ X) ℤ ⥤ CochainComplex (modules Λ X) ℤ)
    (η : 𝟭 _ ⟶ J) (hJ : ∀ M, QuasiIso (η.app M) ∧ (J.obj M).IsKInjective)
    (J' : CochainComplex (modules Λ X) ℤ ⥤ CochainComplex (modules Λ X) ℤ)
    (η' : 𝟭 _ ⟶ J') (hJ' : ∀ M, QuasiIso (η'.app M) ∧ (J'.obj M).IsKInjective)
    (θ : J ⟶ J') : Prop :=
  IsIso (DerivedCategory.Q.map
    (colim.map (Functor.whiskerLeft D (replacementMap Λ f θ)))) ∧
  (∀ M : CochainComplex (modules Λ X) ℤ,
    DerivedCategory.Q.map ((replacementMap Λ f θ).app M) ≫
        (replacementComparison Λ f J' η' hJ' M).hom =
      (replacementComparison Λ f J η hJ M).hom) ∧
  DerivedCategory.Q.map (colim.map (Functor.whiskerLeft D (replacementMap Λ f θ))) ≫
      DerivedCategory.Q.map (colimit.desc (D ⋙ replacedPush Λ f J')
        ((replacedPush Λ f J').mapCocone c)) =
    DerivedCategory.Q.map (colimit.desc (D ⋙ replacedPush Λ f J)
      ((replacedPush Λ f J).mapCocone c)) ≫
      DerivedCategory.Q.map ((replacementMap Λ f θ).app c.pt)

private theorem replacement_comparison_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    {J J' : CochainComplex (modules Λ X) ℤ ⥤ CochainComplex (modules Λ X) ℤ}
    (η : 𝟭 _ ⟶ J) (hJ : ∀ M, QuasiIso (η.app M) ∧ (J.obj M).IsKInjective)
    (η' : 𝟭 _ ⟶ J') (hJ' : ∀ M, QuasiIso (η'.app M) ∧ (J'.obj M).IsKInjective)
    (θ : J ⟶ J') (hθ : η ≫ θ = η') (M : CochainComplex (modules Λ X) ℤ) :
    DerivedCategory.Q.map ((replacementMap Λ f θ).app M) ≫
        (replacementComparison Λ f J' η' hJ' M).hom =
      (replacementComparison Λ f J η hJ M).hom := by
  have := (hJ M).1
  have := (hJ M).2
  have := (hJ' M).1
  have := (hJ' M).2
  have h := right_comparison_naturality (pushforward Λ f) (θ.app M)
  unfold replacementComparison replacedPush
  dsimp only [replacementComparison, Iso.symm_hom, Iso.trans_inv,
    Functor.mapIso_inv, asIso_inv, replacementMap, Functor.whiskerRight_app,
    derivedPushforward]
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp]
  congr 1
  apply congrArg (pushforward Λ f).rightDerivedFunctor.map
  have he : η.app M ≫ θ.app M = η'.app M := NatTrans.congr_app hθ M
  have heQ := congrArg DerivedCategory.Q.map he
  rw [Functor.map_comp] at heQ
  apply (cancel_epi (DerivedCategory.Q.map (η.app M))).mp
  simp only [← Category.assoc, heQ, IsIso.hom_inv_id]

open SheafOfModules in
private theorem replacement_compatible {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ CochainComplex (modules Λ X) ℤ} (c : Cocone D)
    (J : CochainComplex (modules Λ X) ℤ ⥤ CochainComplex (modules Λ X) ℤ)
    (η : 𝟭 _ ⟶ J) (hJ : ∀ M, QuasiIso (η.app M) ∧ (J.obj M).IsKInjective)
    (J' : CochainComplex (modules Λ X) ℤ ⥤ CochainComplex (modules Λ X) ℤ)
    (η' : 𝟭 _ ⟶ J') (hJ' : ∀ M, QuasiIso (η'.app M) ∧ (J'.obj M).IsKInjective)
    (θ : J ⟶ J') (hθ : η ≫ θ = η') :
    ReplacementCompatible Λ f c J η hJ J' η' hJ' θ := by
  have hq (M : CochainComplex (modules Λ X) ℤ) : QuasiIso (θ.app M) := by
    have := (hJ M).1
    have : QuasiIso (η.app M ≫ θ.app M) := by
      rw [show η.app M ≫ θ.app M = η'.app M from NatTrans.congr_app hθ M]
      exact (hJ' M).1
    exact quasiIso_of_comp_left (η.app M) (θ.app M)
  have hpush (M : CochainComplex (modules Λ X) ℤ) :
      QuasiIso ((replacementMap Λ f θ).app M) := by
    have := (hJ M).2
    have := (hJ' M).2
    obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff (θ.app M)).mp (hq M)
    change QuasiIso (((pushforward Λ f).mapHomologicalComplex (.up ℤ)).map (θ.app M))
    rw [← he]
    exact homotopyEquivalences_le_quasiIso _ _ _
      ((pushforward Λ f).mapHomotopyEquiv e).homotopyEquivalences_hom
  have : IsGrothendieckAbelian.{u + 1} (modules Λ Y) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (ring Λ Y)).1
  have : QuasiIso (colim.map (Functor.whiskerLeft D (replacementMap Λ f θ))) :=
    (HomologicalComplex.quasiIso (modules Λ Y) (.up ℤ)).colimMap _
      (fun i ↦ hpush (D.obj i))
  refine ⟨inferInstance, replacement_comparison_map Λ f η hJ η' hJ' θ hθ, ?_⟩
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg DerivedCategory.Q.map
  apply colimit.hom_ext
  intro i
  simp only [colimit.ι_map_assoc, colimit.ι_desc, colimit.ι_desc_assoc,
    Functor.whiskerLeft_app, Functor.mapCocone_ι_app]
  exact ((replacementMap Λ f θ).naturality (c.ι.app i)).symm

/-- Independence via the specified natural zigzag J -> JJ' <- J', for the strict
coefficient tensor cocone. Both colimits and targets are identified by those maps,
and their identifications respect the canonical K-injective computations and all legs.
Source: HRS Lemma 5.3(1), strict specialization of comparison (5.4)
(blueprint: lem-sfb-bounded-flat-tensor-continuity).

Proof: let the augmentation to JJ' be eta followed by eta' at J. Naturality of
eta' makes it equal to eta' followed by J'(eta). The functor J' preserves
quasi-isomorphisms, by naturality and two-out-of-three. Thus both arrows of the
zigzag are quasi-isomorphisms between K-injectives. By
lem-weil-pbc-kinjective-hom-derived they are homotopy equivalences. Additive
pushforward preserves homotopies, so their images are quasi-isomorphisms.
Filtered colimits of module sheaves are exact; by
src-weil-homology-preserves-exact-colimits their degreewise colimits are again
quasi-isomorphisms. The uniqueness of the K-injective computation identifies the
normalized replacementComparison maps. Finally the universal property of the
ordinary complex colimit, tested on each injection, gives the displayed square.
This proves step 8 of the node's proof without imposing any bound on J(E_i).
-/
theorem replacement_independence
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (P : I ⥤ modules Λ Y) (c : Cocone P)
    (Kc : CochainComplex (modules Λ X) ℤ)
    (J : CochainComplex (modules Λ X) ℤ ⥤ CochainComplex (modules Λ X) ℤ)
    (η : 𝟭 _ ⟶ J) (hJ : ∀ M, QuasiIso (η.app M) ∧ (J.obj M).IsKInjective)
    (J' : CochainComplex (modules Λ X) ℤ ⥤ CochainComplex (modules Λ X) ℤ)
    (η' : 𝟭 _ ⟶ J') (hJ' : ∀ M, QuasiIso (η'.app M) ∧ (J'.obj M).IsKInjective) :
    ∃ hJJ' : ∀ M,
        QuasiIso ((η ≫ Functor.whiskerLeft J η').app M) ∧
          ((J ⋙ J').obj M).IsKInjective,
      ReplacementCompatible Λ f ((pulledTensor Λ f Kc).mapCocone c)
        J η hJ (J ⋙ J') (η ≫ Functor.whiskerLeft J η') hJJ'
        (Functor.whiskerLeft J η') ∧
      ReplacementCompatible Λ f ((pulledTensor Λ f Kc).mapCocone c)
        J' η' hJ' (J ⋙ J') (η ≫ Functor.whiskerLeft J η') hJJ'
        (Functor.whiskerRight η J') := by
  let hJJ' : ∀ M,
      QuasiIso ((η ≫ Functor.whiskerLeft J η').app M) ∧
        ((J ⋙ J').obj M).IsKInjective := by
    intro M
    have := (hJ M).1
    have := (hJ' (J.obj M)).1
    change QuasiIso (η.app M ≫ η'.app (J.obj M)) ∧ _
    exact ⟨inferInstance, (hJ' (J.obj M)).2⟩
  refine ⟨hJJ', ?_, ?_⟩
  · exact replacement_compatible Λ f _ J η hJ (J ⋙ J')
      (η ≫ Functor.whiskerLeft J η') hJJ' (Functor.whiskerLeft J η') rfl
  · apply replacement_compatible Λ f _ J' η' hJ' (J ⋙ J')
      (η ≫ Functor.whiskerLeft J η') hJJ' (Functor.whiskerRight η J')
    apply NatTrans.ext
    funext M
    exact (η'.naturality (η.app M)).symm


end AlgebraicGeometry.ProEtale.BoundedFlatTensorContinuity
