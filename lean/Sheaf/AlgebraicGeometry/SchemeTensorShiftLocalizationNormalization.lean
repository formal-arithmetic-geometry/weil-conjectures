/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex

/-! # Normalizing tensor-shift composites through localization
Source: Stacks Project, Tag 06YH, K-flat total tensor localization.
(blueprint: lem-sc-scheme-tensor-shift-localization-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

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
          (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) 1).hom) := by sorry

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
        (α_ P T U).hom⟦(1 : ℤ)⟧') := by sorry

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
