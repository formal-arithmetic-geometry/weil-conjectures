/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import Sheaf.AlgebraicGeometry.SchemeTensorShiftBinaryLocalizationSquare

/-! # Normalizing tensor-shift composites through localization
Source: Stacks Project, Tag 06YH, K-flat total tensor localization.
(blueprint: lem-sc-scheme-tensor-shift-localization-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w u' v'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

private theorem first_generic
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [MonoidalCategory C] [MonoidalCategory D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.LaxMonoidal] [F.CommShift ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [(curriedTensor D).CommShift₂Int]
    (P T U : C) (σ : P⟦(1 : ℤ)⟧ ⊗ (T ⊗ U) ⟶ (P ⊗ (T ⊗ U))⟦(1 : ℤ)⟧)
    (hs : ((tensorRight (F.obj (T ⊗ U))).commShiftIso (1 : ℤ)).hom.app (F.obj P) ≫
      (Functor.LaxMonoidal.μ F P (T ⊗ U))⟦(1 : ℤ)⟧' ≫
      (F.commShiftIso (1 : ℤ)).inv.app (P ⊗ (T ⊗ U)) =
      ((F.commShiftIso (1 : ℤ)).inv.app P) ▷ F.obj (T ⊗ U) ≫
      Functor.LaxMonoidal.μ F (P⟦(1 : ℤ)⟧) (T ⊗ U) ≫ F.map σ) :
    (α_ (F.obj P⟦(1 : ℤ)⟧) (F.obj T) (F.obj U)).hom ≫
      ((tensorRight (F.obj T ⊗ F.obj U)).commShiftIso (1 : ℤ)).hom.app (F.obj P) ≫
      (F.obj P ◁ Functor.LaxMonoidal.μ F T U ≫
        Functor.LaxMonoidal.μ F P (T ⊗ U))⟦(1 : ℤ)⟧' ≫
      (F.commShiftIso (1 : ℤ)).inv.app (P ⊗ (T ⊗ U)) =
    (((F.commShiftIso (1 : ℤ)).inv.app P) ▷ F.obj T) ▷ F.obj U ≫
      (Functor.LaxMonoidal.μ F (P⟦(1 : ℤ)⟧) T) ▷ F.obj U ≫
      Functor.LaxMonoidal.μ F (P⟦(1 : ℤ)⟧ ⊗ T) U ≫
      F.map ((α_ (P⟦(1 : ℤ)⟧) T U).hom ≫ σ) := by
  have hn := NatTrans.shift_app_comm
    ((curriedTensor D).flip.map (Functor.LaxMonoidal.μ F T U)) (1 : ℤ) (F.obj P)
  change ((tensorRight (F.obj T ⊗ F.obj U)).commShiftIso (1 : ℤ)).hom.app (F.obj P) ≫
      (F.obj P ◁ Functor.LaxMonoidal.μ F T U)⟦(1 : ℤ)⟧' =
    F.obj P⟦(1 : ℤ)⟧ ◁ Functor.LaxMonoidal.μ F T U ≫
      ((tensorRight (F.obj (T ⊗ U))).commShiftIso (1 : ℤ)).hom.app (F.obj P) at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, hs, whisker_exchange_assoc,
    ← associator_naturality_left_assoc]
  simp only [Functor.comp_obj]
  rw [← Functor.LaxMonoidal.associativity_assoc F (P⟦(1 : ℤ)⟧) T U]

private theorem second_generic
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [MonoidalCategory C] [MonoidalCategory D] [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.LaxMonoidal] [F.CommShift ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [(curriedTensor D).CommShift₂Int]
    (P T U : C) (σ₁ : P⟦(1 : ℤ)⟧ ⊗ T ⟶ (P ⊗ T)⟦(1 : ℤ)⟧)
    (σ₂ : (P ⊗ T)⟦(1 : ℤ)⟧ ⊗ U ⟶ ((P ⊗ T) ⊗ U)⟦(1 : ℤ)⟧)
    (hs₁ : ((tensorRight (F.obj T)).commShiftIso (1 : ℤ)).hom.app (F.obj P) ≫
      (Functor.LaxMonoidal.μ F P T)⟦(1 : ℤ)⟧' ≫
      (F.commShiftIso (1 : ℤ)).inv.app (P ⊗ T) =
      ((F.commShiftIso (1 : ℤ)).inv.app P) ▷ F.obj T ≫
      Functor.LaxMonoidal.μ F (P⟦(1 : ℤ)⟧) T ≫ F.map σ₁)
    (hs₂ : ((tensorRight (F.obj U)).commShiftIso (1 : ℤ)).hom.app (F.obj (P ⊗ T)) ≫
      (Functor.LaxMonoidal.μ F (P ⊗ T) U)⟦(1 : ℤ)⟧' ≫
      (F.commShiftIso (1 : ℤ)).inv.app ((P ⊗ T) ⊗ U) =
      ((F.commShiftIso (1 : ℤ)).inv.app (P ⊗ T)) ▷ F.obj U ≫
      Functor.LaxMonoidal.μ F ((P ⊗ T)⟦(1 : ℤ)⟧) U ≫ F.map σ₂) :
    (((tensorRight (F.obj T)).commShiftIso (1 : ℤ)).hom.app (F.obj P)) ▷ F.obj U ≫
      ((tensorRight (F.obj U)).commShiftIso (1 : ℤ)).hom.app (F.obj P ⊗ F.obj T) ≫
      (α_ (F.obj P) (F.obj T) (F.obj U)).hom⟦(1 : ℤ)⟧' ≫
      (F.obj P ◁ Functor.LaxMonoidal.μ F T U ≫
        Functor.LaxMonoidal.μ F P (T ⊗ U))⟦(1 : ℤ)⟧' ≫
      (F.commShiftIso (1 : ℤ)).inv.app (P ⊗ (T ⊗ U)) =
    (((F.commShiftIso (1 : ℤ)).inv.app P) ▷ F.obj T) ▷ F.obj U ≫
      (Functor.LaxMonoidal.μ F (P⟦(1 : ℤ)⟧) T) ▷ F.obj U ≫
      Functor.LaxMonoidal.μ F (P⟦(1 : ℤ)⟧ ⊗ T) U ≫
      F.map (σ₁ ▷ U ≫ σ₂ ≫ (α_ P T U).hom⟦(1 : ℤ)⟧') := by
  have hn := (tensorRight (F.obj U)).commShiftIso_hom_naturality
    (Functor.LaxMonoidal.μ F P T) (1 : ℤ)
  change (Functor.LaxMonoidal.μ F P T)⟦(1 : ℤ)⟧' ▷ F.obj U ≫
      ((tensorRight (F.obj U)).commShiftIso (1 : ℤ)).hom.app (F.obj (P ⊗ T)) =
    ((tensorRight (F.obj U)).commShiftIso (1 : ℤ)).hom.app (F.obj P ⊗ F.obj T) ≫
      (Functor.LaxMonoidal.μ F P T ▷ F.obj U)⟦(1 : ℤ)⟧' at hn
  have ha := congrArg (fun f ↦ (shiftFunctor D (1 : ℤ)).map f)
    (Functor.LaxMonoidal.associativity F P T U)
  simp only [Functor.map_comp] at ha
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% ha, ← reassoc_of% hn,
    F.commShiftIso_inv_naturality (α_ P T U).hom (1 : ℤ), reassoc_of% hs₂]
  have hw := congrArg (fun f ↦ f ▷ F.obj U) hs₁
  simp only [comp_whiskerRight] at hw
  rw [reassoc_of% hw, Functor.LaxMonoidal.μ_natural_left_assoc]


open Functor.LaxMonoidal in
private theorem tensorator_isIso
    (C : Type*) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{u} C]
    [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C]
    [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    [HasColimitsOfSize.{0, 0} C]
    [DerivedCategory.Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (.up ℤ))]
    (P T : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    IsIso (μ DerivedCategory.Q P T) := by
  have : IsIso (μ DerivedCategory.Qh
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)
      ((HomotopyCategory.quotient C (.up ℤ)).obj T)) :=
    inferInstanceAs (IsIso
      (((DerivedCategory.IndependentTensorShift.TensorCommShift₂.liftingIsoHom C).app
        ⟨P, hP⟩).app T))
  change IsIso
    (((DerivedCategory.quotientCompQhIso C).inv.app P ⊗ₘ
        (DerivedCategory.quotientCompQhIso C).inv.app T) ≫
      μ (HomotopyCategory.quotient C (.up ℤ) ⋙ DerivedCategory.Qh) P T ≫
      (DerivedCategory.quotientCompQhIso C).hom.app (P ⊗ T))
  rw [Functor.LaxMonoidal.comp_μ]
  infer_instance

variable (X : Scheme.{u})

noncomputable local instance :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance :
    SymmetricCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.symmetricCategory X.sheaf
local instance : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
noncomputable local instance :
    MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
local instance : IsGrothendieckAbelian.{u}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
local instance : HasColimitsOfSize.{0, 0}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := hasColimitsOfSizeShrink.{0, 0, u, u} _
local instance : Abelian.HasFunctorialFlatResolution
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  schemeModule_hasFunctorialFlatResolution X
variable [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

local instance : DerivedCategory.Qh.HasDerivedMonoidalCategory
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :=
  DerivedCategory.hasDerivedMonoidalCategory _

local instance (A B : GradedObject ℤ
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))) : A.HasTensor B := inferInstance

local instance (A B C D : GradedObject ℤ
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    GradedObject.HasTensor₄ObjExt A B C D := inferInstance

local instance (A B C : GradedObject ℤ
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    GradedObject.HasGoodTensor₁₂Tensor A B C := inferInstance

local instance (A B C : GradedObject ℤ
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    GradedObject.HasGoodTensorTensor₂₃ A B C := inferInstance

local instance (A B : CochainComplex
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    CochainComplex.HasMapBifunctor A B
      (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) := inferInstance

noncomputable local instance : MonoidalCategory
    (CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) := inferInstance

noncomputable local instance : MonoidalCategory (schemeDerivedCategory X) :=
  schemeDerivedTensorMonoidal X

noncomputable local instance :
    (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).LaxMonoidal :=
  Functor.LaxMonoidal.ofIso (DerivedCategory.quotientCompQhIso _)

omit [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] in
private theorem upstreamKFlat
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P) :
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).kFlat P := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic]
  intro N hN
  obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
  rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
  have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor N P (curriedTensor _))).2 (hP N hN)
  exact ⟨(HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr, hr⟩

open Functor.LaxMonoidal in
/-- The comparison from a translated derived triple tensor to its total tensor representative.
Source: Stacks Project, Tag 06YH.
(blueprint: lem-sc-scheme-tensor-shift-localization-normalization). -/
noncomputable def schemeTensorShiftSourceComparison
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (DerivedCategory.Q.obj P⟦(1 : ℤ)⟧ ⊗ DerivedCategory.Q.obj T) ⊗
        DerivedCategory.Q.obj U ⟶ DerivedCategory.Q.obj ((P⟦(1 : ℤ)⟧ ⊗ T) ⊗ U) :=
  (((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app P) ▷ DerivedCategory.Q.obj T) ▷
      DerivedCategory.Q.obj U ≫
    (μ DerivedCategory.Q (P⟦(1 : ℤ)⟧) T) ▷ DerivedCategory.Q.obj U ≫
    μ DerivedCategory.Q (P⟦(1 : ℤ)⟧ ⊗ T) U

open Functor.LaxMonoidal in
/-- The comparison from the translated right-associated derived tensor to localization.
Source: Stacks Project, Tag 06YH.
(blueprint: lem-sc-scheme-tensor-shift-localization-normalization). -/
noncomputable def schemeTensorShiftTargetComparison
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (DerivedCategory.Q.obj P ⊗ (DerivedCategory.Q.obj T ⊗ DerivedCategory.Q.obj U))⟦(1 : ℤ)⟧ ⟶
      DerivedCategory.Q.obj ((P ⊗ (T ⊗ U))⟦(1 : ℤ)⟧) :=
  (DerivedCategory.Q.obj P ◁ μ DerivedCategory.Q T U ≫
    μ DerivedCategory.Q P (T ⊗ U))⟦(1 : ℤ)⟧' ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app (P ⊗ (T ⊗ U))

/- The target comparison is invertible for K-flat representatives.  The proof uses
the K-flat localization comparison theorem: each tensorator involving a K-flat
factor is an isomorphism, as are the shift comparison maps.  The displayed map is
their composite, so `infer_instance` supplies its `IsIso` instance after unfolding.
Source: Stacks Project, Tag 06YH, localization normalization calculation.
(blueprint: aux-sc-target-comparison-isIso) -/
set_option linter.unusedVariables false in
theorem schemeTensorShift_targetComparison_isIso
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (hT : CochainComplex.IsKFlat (R := X.sheaf) T)
    (hU : CochainComplex.IsKFlat (R := X.sheaf) U) :
    letI := schemeCanonicalTensorShift X
    letI : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
      fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
    IsIso (schemeTensorShiftTargetComparison X P T U) := by
  have hp := upstreamKFlat X P hP
  have ht := upstreamKFlat X T hT
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q T U) :=
    tensorator_isIso (SheafOfModules.{u} (moduleRings X.toRingedSpace)) T U ht
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P (T ⊗ U)) :=
    tensorator_isIso (SheafOfModules.{u} (moduleRings X.toRingedSpace)) P (T ⊗ U) hp
  dsimp only [schemeTensorShiftTargetComparison]
  infer_instance

set_option linter.unusedVariables false in
/-- Expanded first normalization coherence intermediate.
The proof unfolds all local abbreviations in the localization calculation.
(blueprint: aux-sc-target-comparison-first-core). -/
theorem schemeTensorShift_first_normalization_core
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (hT : CochainComplex.IsKFlat (R := X.sheaf) T)
    (hU : CochainComplex.IsKFlat (R := X.sheaf) U) :
    letI := schemeCanonicalTensorShift X
    letI : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
      fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
    ((α_ (DerivedCategory.Q.obj P⟦(1 : ℤ)⟧) (DerivedCategory.Q.obj T)
      (DerivedCategory.Q.obj U)).hom ≫
      ((tensorRight (DerivedCategory.Q.obj T ⊗ DerivedCategory.Q.obj U)).commShiftIso
        (1 : ℤ)).hom.app (DerivedCategory.Q.obj P)) ≫
      schemeTensorShiftTargetComparison X P T U =
      schemeTensorShiftSourceComparison X P T U ≫
      DerivedCategory.Q.map ((α_ (P⟦(1 : ℤ)⟧) T U).hom ≫
        (CochainComplex.mapBifunctorShift₁Iso P (T ⊗ U)
          (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom) := by
  let := schemeCanonicalTensorShift X
  let : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
    fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
  simpa only [schemeTensorShiftTargetComparison, schemeTensorShiftSourceComparison,
    Category.assoc] using first_generic DerivedCategory.Q P T U
    (CochainComplex.mapBifunctorShift₁Iso P (T ⊗ U)
      (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom
    (schemeTensorShift_binary_localization_square X P (T ⊗ U) (upstreamKFlat X P hP))

theorem schemeTensorShift_first_normalization
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (hT : CochainComplex.IsKFlat (R := X.sheaf) T)
    (hU : CochainComplex.IsKFlat (R := X.sheaf) U) :
    letI := schemeCanonicalTensorShift X
    letI : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
      fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
    let A := DerivedCategory.Q.obj P
    let K := DerivedCategory.Q.obj T
    let M := DerivedCategory.Q.obj U
    let c := schemeTensorShiftTargetComparison X P T U
    let v := schemeTensorShiftSourceComparison X P T U
    ((α_ (A⟦(1 : ℤ)⟧) K M).hom ≫
        ((tensorRight (K ⊗ M)).commShiftIso (1 : ℤ)).hom.app A) ≫ c =
      v ≫ DerivedCategory.Q.map ((α_ (P⟦(1 : ℤ)⟧) T U).hom ≫
        (CochainComplex.mapBifunctorShift₁Iso P (T ⊗ U)
          (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom) := by
  simpa using schemeTensorShift_first_normalization_core X P T U hP hT hU

set_option linter.unusedVariables false in
/-- Second route normalization component.  Apply the localization shift square
first to `P,T` and then to `P ⊗ T,U`; K-flatness is preserved by tensoring.
Use lax monoidal associativity and naturality of the shift comparison to move
the two tensorators through the translated factors.  Their composite is the
localized complex associator shown on the right, by functoriality of `Q`.
Source: Stacks Project, Tag 06YH, second localization normalization calculation.
(blueprint: aux-sc-target-comparison-second) -/
theorem schemeTensorShift_second_normalization
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (hT : CochainComplex.IsKFlat (R := X.sheaf) T)
    (hU : CochainComplex.IsKFlat (R := X.sheaf) U) :
    letI := schemeCanonicalTensorShift X
    letI : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
      fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
    let A := DerivedCategory.Q.obj P
    let K := DerivedCategory.Q.obj T
    let M := DerivedCategory.Q.obj U
    let c := schemeTensorShiftTargetComparison X P T U
    let v := schemeTensorShiftSourceComparison X P T U
    ((((tensorRight K).commShiftIso (1 : ℤ)).hom.app A) ▷ M ≫
        ((tensorRight M).commShiftIso (1 : ℤ)).hom.app (A ⊗ K) ≫
        (α_ A K M).hom⟦(1 : ℤ)⟧') ≫ c =
      v ≫ DerivedCategory.Q.map
        ((CochainComplex.mapBifunctorShift₁Iso P T
          (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom ▷ U ≫
        (CochainComplex.mapBifunctorShift₁Iso (P ⊗ T) U
          (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom ≫
        (α_ P T U).hom⟦(1 : ℤ)⟧') := by
  let := schemeCanonicalTensorShift X
  let : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
    fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
  have hp := upstreamKFlat X P hP
  have ht := upstreamKFlat X T hT
  have hpt : (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)).kFlat (P ⊗ T) :=
    ObjectProperty.prop_tensor hp ht
  have hs₁ := schemeTensorShift_binary_localization_square X P T hp
  have hs₂ := schemeTensorShift_binary_localization_square X (P ⊗ T) U hpt
  simpa only [schemeTensorShiftTargetComparison, schemeTensorShiftSourceComparison,
    Category.assoc] using second_generic DerivedCategory.Q P T U
    (CochainComplex.mapBifunctorShift₁Iso P T
      (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom
    (CochainComplex.mapBifunctorShift₁Iso (P ⊗ T) U
      (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom hs₁ hs₂

theorem schemeTensorShift_localization_normalization
    (P T U : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (hT : CochainComplex.IsKFlat (R := X.sheaf) T)
    (hU : CochainComplex.IsKFlat (R := X.sheaf) U) :
    letI := schemeCanonicalTensorShift X
    letI : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
      fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
    let A := DerivedCategory.Q.obj P
    let K := DerivedCategory.Q.obj T
    let M := DerivedCategory.Q.obj U
    let c := schemeTensorShiftTargetComparison X P T U
    let v := schemeTensorShiftSourceComparison X P T U
    IsIso c ∧
      ((α_ (A⟦(1 : ℤ)⟧) K M).hom ≫
          ((tensorRight (K ⊗ M)).commShiftIso (1 : ℤ)).hom.app A) ≫ c =
        v ≫ DerivedCategory.Q.map ((α_ (P⟦(1 : ℤ)⟧) T U).hom ≫
          (CochainComplex.mapBifunctorShift₁Iso P (T ⊗ U)
            (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom) ∧
      ((((tensorRight K).commShiftIso (1 : ℤ)).hom.app A) ▷ M ≫
          ((tensorRight M).commShiftIso (1 : ℤ)).hom.app (A ⊗ K) ≫
          (α_ A K M).hom⟦(1 : ℤ)⟧') ≫ c =
        v ≫ DerivedCategory.Q.map
          ((CochainComplex.mapBifunctorShift₁Iso P T
            (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom ▷ U ≫
          (CochainComplex.mapBifunctorShift₁Iso (P ⊗ T) U
            (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom ≫
          (α_ P T U).hom⟦(1 : ℤ)⟧') := by
  dsimp
  exact ⟨schemeTensorShift_targetComparison_isIso X P T U hP hT hU,
    schemeTensorShift_first_normalization X P T U hP hT hU,
    schemeTensorShift_second_normalization X P T U hP hT hU⟩

end AlgebraicGeometry
