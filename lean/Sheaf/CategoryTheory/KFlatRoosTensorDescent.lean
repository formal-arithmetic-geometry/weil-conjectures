/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.KFlatAugmentedRoosDefinitions
import WeilConjectures.Mathlib.CategoryTheory.Shift.Localization
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.KFlatRoosDerivedComparison

/-! # Localization of total tensor by an arbitrary K-flat complex

Source: Stacks sites-cohomology.tex Tags 06YM, 06YP, 06YS and 06YT.
(blueprint: lem-sfb-kflat-roos-tensor-descent).

K-flat tensor preserves quasi-isomorphisms, so localization supplies its functor,
representative isomorphism and transformations in the first argument. To invert a
quasi-isomorphism between K-flat arguments, resolve the other factor K-flatly and
use the natural tensor square: its other three sides are quasi-isomorphisms.
The signed shift and cone isomorphisms descend through homotopy localization and
supply the triangulated functor structure. The same localization works levelwise
for strict towers because their quasi-isomorphisms are detected by evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex
namespace CategoryTheory.KFlatAugmentedRoos
open SheafOfModules.TotalTensorSigns
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
  [HasDerivedCategory.{w} (Modules R)]

omit [HasDerivedCategory (Modules R)] in
theorem tensor_quasiIso (A : CochainComplex (Modules R) ℤ)
    (hA : IsKFlatIndependentCoefficients A)
    {X Y : CochainComplex (Modules R) ℤ} (f : X ⟶ Y) (hf : QuasiIso f) :
    QuasiIso (((total R).obj A).map f) ∧ QuasiIso (((total R).flip.obj A).map f) := by
  exact ((totalTensorHomotopyConeSigns R).2.2.2.2.2.2.1 A hA).1 X Y f hf

theorem tensor_inverts (A : CochainComplex (Modules R) ℤ)
    (hA : IsKFlatIndependentCoefficients A) :
    (HomologicalComplex.quasiIso (Modules R) (.up ℤ)).IsInvertedBy
      ((total R).obj A ⋙ DerivedCategory.Q.{w}) := by
  intro X Y f hf
  have := (tensor_quasiIso R A hA f hf).1
  change IsIso (DerivedCategory.Q.map (((total R).obj A).map f))
  infer_instance

section TowerTensor
variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ Modules R)]

omit [HasDerivedCategory (Modules R)] in
theorem towerTensor_inverts (A : CochainComplex (Modules R) ℤ)
    (hA : IsKFlatIndependentCoefficients A) :
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Modules R) (.up ℤ)).IsInvertedBy
      (tower ((total R).obj A) ⋙ DerivedCategory.Q.{w}) := by
  intro X Y f hf
  have := tower_quasiIso ((total R).obj A)
    (fun U V g hg ↦ (tensor_quasiIso R A hA g hg).1) f hf
  change IsIso (DerivedCategory.Q.map ((tower ((total R).obj A)).map f))
  infer_instance

/-- The canonical localization of tensor at every tower level. -/
def localizedTowerTensor (K : {A : CochainComplex (Modules R) ℤ //
    IsKFlatIndependentCoefficients A}) : DerivedCategory.{w} (ℕᵒᵖ ⥤ Modules R) ⥤
      DerivedCategory.{w} (ℕᵒᵖ ⥤ Modules R) :=
  Localization.lift (tower ((total R).obj K.val) ⋙ DerivedCategory.Q.{w})
    (towerTensor_inverts R K.val K.property) DerivedCategory.Q.{w}

/-- The representative comparison for localization of tower tensor. -/
def localizedTowerTensorIso (K : {A : CochainComplex (Modules R) ℤ //
    IsKFlatIndependentCoefficients A}) :
    DerivedCategory.Q.{w} ⋙ localizedTowerTensor R K ≅
      tower ((total R).obj K.val) ⋙ DerivedCategory.Q.{w} :=
  Localization.fac _ (towerTensor_inverts R K.val K.property) _

end TowerTensor

/-- The localization of tensor by a K-flat complex.
Source: Stacks Tags 06YM and 06YP
(blueprint: lem-sfb-kflat-roos-tensor-descent). -/
def localizedTensor (K : {A : CochainComplex (Modules R) ℤ //
    IsKFlatIndependentCoefficients A}) : DerivedCategory.{w} (Modules R) ⥤
      DerivedCategory.{w} (Modules R) :=
  Localization.lift ((total R).obj K.val ⋙ DerivedCategory.Q.{w})
    (tensor_inverts R K.val K.property) DerivedCategory.Q.{w}

/-- The canonical representative comparison for localized K-flat tensor.
Source: Stacks Tag 06YP (blueprint: lem-sfb-kflat-roos-tensor-descent). -/
def localizedTensorIso (K : {A : CochainComplex (Modules R) ℤ //
    IsKFlatIndependentCoefficients A}) :
    DerivedCategory.Q.{w} ⋙ localizedTensor R K ≅
      (total R).obj K.val ⋙ DerivedCategory.Q.{w} :=
  Localization.fac _ (tensor_inverts R K.val K.property) _

/-- The localized transformation in the K-flat argument.
Source: Stacks Tag 06YT (blueprint: lem-sfb-kflat-roos-tensor-descent). -/
def localizedTensorMap
    (K L : {A : CochainComplex (Modules R) ℤ // IsKFlatIndependentCoefficients A})
    (α : K.val ⟶ L.val) : localizedTensor R K ⟶ localizedTensor R L :=
  let : Localization.Lifting DerivedCategory.Q.{w}
      (HomologicalComplex.quasiIso (Modules R) (.up ℤ))
      ((total R).obj K.val ⋙ DerivedCategory.Q.{w}) (localizedTensor R K) :=
    ⟨localizedTensorIso R K⟩
  let : Localization.Lifting DerivedCategory.Q.{w}
      (HomologicalComplex.quasiIso (Modules R) (.up ℤ))
      ((total R).obj L.val ⋙ DerivedCategory.Q.{w}) (localizedTensor R L) :=
    ⟨localizedTensorIso R L⟩
  Localization.liftNatTrans DerivedCategory.Q.{w}
    (HomologicalComplex.quasiIso (Modules R) (.up ℤ)) _ _ _ _
      (Functor.whiskerRight ((total R).map α) DerivedCategory.Q.{w})

theorem localizedTensorMap_fac
    (K L : {A : CochainComplex (Modules R) ℤ // IsKFlatIndependentCoefficients A})
    (α : K.val ⟶ L.val) (U : CochainComplex (Modules R) ℤ) :
    (localizedTensorMap R K L α).app (DerivedCategory.Q.obj U) ≫
        (localizedTensorIso R L).hom.app U =
      (localizedTensorIso R K).hom.app U ≫
        DerivedCategory.Q.map (((total R).map α).app U) := by
  dsimp only [localizedTensorMap]
  rw [Localization.liftNatTrans_app]
  simp only [Functor.whiskerRight_app, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]

omit [HasDerivedCategory (Modules R)] in
theorem tensor_quasiIso_first
    (K L : {A : CochainComplex (Modules R) ℤ // IsKFlatIndependentCoefficients A})
    (α : K.val ⟶ L.val) (hα : QuasiIso α) (U : CochainComplex (Modules R) ℤ) :
    QuasiIso (((total R).map α).app U) := by
  obtain ⟨P, p, hP, _, hp, _⟩ := exists_isKFlatResolutionIndependentCoefficients U
  have := hp
  have h₁ := (tensor_quasiIso R K.val K.property p hp).1
  have h₂ := (tensor_quasiIso R L.val L.property p hp).1
  have h₃ : QuasiIso (((total R).map α).app P) :=
    (tensor_quasiIso R P hP α hα).2
  have he : ((total R).obj K.val).map p ≫ ((total R).map α).app U =
      ((total R).map α).app P ≫ ((total R).obj L.val).map p :=
    ((total R).map α).naturality p
  rw [← quasiIso_iff_comp_left (((total R).obj K.val).map p), he]
  infer_instance

theorem localizedTensorMap_isIso
    (K L : {A : CochainComplex (Modules R) ℤ // IsKFlatIndependentCoefficients A})
    (α : K.val ⟶ L.val) (hα : QuasiIso α) : IsIso (localizedTensorMap R K L α) := by
  have h (U : CochainComplex (Modules R) ℤ) :
      IsIso ((localizedTensorMap R K L α).app (DerivedCategory.Q.obj U)) := by
    have := tensor_quasiIso_first R K L α hα U
    have hi : IsIso ((localizedTensorMap R K L α).app (DerivedCategory.Q.obj U) ≫
        (localizedTensorIso R L).hom.app U) := by
      rw [localizedTensorMap_fac]
      infer_instance
    exact (isIso_comp_right_iff _ ((localizedTensorIso R L).hom.app U)).1 hi
  have hi (U : DerivedCategory.{w} (Modules R)) :
      IsIso ((localizedTensorMap R K L α).app U) := by
    exact (NatTrans.isIso_app_iff_of_iso (localizedTensorMap R K L α)
      (DerivedCategory.Q.objObjPreimageIso U)).1 (h _)
  exact NatIso.isIso_of_isIso_app _

/-- The homotopy representative of localized tensor. -/
def localizedTensorHomotopyIso
    (K : {A : CochainComplex (Modules R) ℤ // IsKFlatIndependentCoefficients A}) :
    DerivedCategory.Qh.{w} ⋙ localizedTensor R K ≅
      (homotopyTensor R).obj ((HomotopyCategory.quotient _ _).obj K.val) ⋙
        DerivedCategory.Qh.{w} :=
  Quotient.natIsoLift _
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso (Modules R)) _ ≪≫
      localizedTensorIso R K ≪≫
        Functor.isoWhiskerLeft ((total R).obj K.val)
          (DerivedCategory.quotientCompQhIso (Modules R)).symm)

/-- The coherent shifts on localized total tensor. -/
@[instance_reducible]
def localizedTensorShift
    (K : {A : CochainComplex (Modules R) ℤ // IsKFlatIndependentCoefficients A}) :
    (localizedTensor R K).CommShift ℤ :=
  let : Localization.Lifting DerivedCategory.Qh.{w}
      (HomotopyCategory.quasiIso (Modules R) (.up ℤ))
      ((homotopyTensor R).obj ((HomotopyCategory.quotient _ _).obj K.val) ⋙
        DerivedCategory.Qh.{w}) (localizedTensor R K) :=
    ⟨localizedTensorHomotopyIso R K⟩
  Functor.commShiftOfLocalization DerivedCategory.Qh.{w}
    (HomotopyCategory.quasiIso (Modules R) (.up ℤ)) ℤ
    ((homotopyTensor R).obj ((HomotopyCategory.quotient _ _).obj K.val) ⋙
      DerivedCategory.Qh.{w}) (localizedTensor R K)

/-- Localized total tensor carries distinguished triangles to distinguished triangles. -/
theorem localizedTensor_triangulated
    (K : {A : CochainComplex (Modules R) ℤ // IsKFlatIndependentCoefficients A}) :
    let := localizedTensorShift R K
    (localizedTensor R K).IsTriangulated := by
  let := localizedTensorShift R K
  let : Localization.Lifting DerivedCategory.Qh.{w}
      (HomotopyCategory.quasiIso (Modules R) (.up ℤ))
      ((homotopyTensor R).obj ((HomotopyCategory.quotient _ _).obj K.val) ⋙
        DerivedCategory.Qh.{w}) (localizedTensor R K) :=
    ⟨localizedTensorHomotopyIso R K⟩
  have := Localization.essSurj_mapArrow DerivedCategory.Qh.{w}
    (HomotopyCategory.quasiIso (Modules R) (.up ℤ))
  exact Functor.isTriangulated_of_precomp_iso
    (Localization.Lifting.iso DerivedCategory.Qh.{w}
      (HomotopyCategory.quasiIso (Modules R) (.up ℤ))
      ((homotopyTensor R).obj ((HomotopyCategory.quotient _ _).obj K.val) ⋙
        DerivedCategory.Qh.{w}) (localizedTensor R K))

end CategoryTheory.KFlatAugmentedRoos
