/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitTensorSystemData
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorCoherentConstruction
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitRegularMultiplicationCoordinates
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitRegularPullbackMultiplication
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # Multiplication determines the normalized system pullback unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.CompletedUnitPullback
open CategoryTheory.MonoidalCategory

private theorem unit_multiplication_iso_unique
    {D : Type*} [Category* D] [MonoidalCategory D]
    {A : D} (m : A ⊗ A ⟶ A) (e d : A ≅ 𝟙_ D)
    (he : m ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ (λ_ (𝟙_ D)).hom)
    (hd : m ≫ d.hom = (d.hom ⊗ₘ d.hom) ≫ (λ_ (𝟙_ D)).hom) :
    e.hom = d.hom := by
  let a := e.symm ≪≫ d
  have ht : (λ_ (𝟙_ D)).hom ≫ a.hom =
      (a.hom ⊗ₘ a.hom) ≫ (λ_ (𝟙_ D)).hom := by
    have he' := congrArg (fun z ↦ (e.inv ⊗ₘ e.inv) ≫ z ≫ e.inv) he
    simp only [Category.assoc, tensorHom_comp_tensorHom_assoc,
      Iso.inv_hom_id, tensorHom_id, id_whiskerRight, Category.id_comp,
      Iso.hom_inv_id, Category.comp_id] at he'
    have hd' := congrArg (fun z ↦ (e.inv ⊗ₘ e.inv) ≫ z) hd
    rw [← Category.assoc, he'] at hd'
    simpa only [a, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      tensorHom_comp_tensorHom_assoc] using hd'
  have hh : (a.hom ⊗ₘ a.hom) ≫ (λ_ (𝟙_ D)).hom =
      (λ_ (𝟙_ D)).hom ≫ a.hom ≫ a.hom := by
    rw [MonoidalCategory.tensorHom_def, Category.assoc, leftUnitor_naturality]
    rw [unitors_equal, rightUnitor_naturality_assoc, ← unitors_equal]
  rw [hh] at ht
  have hi : 𝟙 _ = a.hom := by
    apply (cancel_epi ((λ_ (𝟙_ D)).hom ≫ a.hom)).mp
    simpa only [Category.assoc, Category.comp_id] using ht
  have hj := congrArg (fun z ↦ e.hom ≫ z) hi
  simpa [a] using hj

private theorem transport_regular_multiplication
    {C D : Type*} [Category* C] [MonoidalCategory C]
    [Category* D] [MonoidalCategory D]
    (F : C ⥤ D) (μ : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    {U : C} {V : D} (e : 𝟙_ C ≅ U) (d : 𝟙_ D ≅ V)
    (m : U ⊗ U ⟶ U) (n : V ⊗ V ⟶ V) (r : F.obj U ≅ V)
    (he : (λ_ (𝟙_ C)).hom ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ m)
    (hd : (λ_ (𝟙_ D)).hom ≫ d.hom = (d.hom ⊗ₘ d.hom) ≫ n)
    (hr : F.map m ≫ r.hom = (μ.app (U, U)).hom ≫ (r.hom ⊗ₘ r.hom) ≫ n) :
    let δ := F.mapIso e ≪≫ r ≪≫ d.symm
    F.map (λ_ (𝟙_ C)).hom ≫ δ.hom =
      (μ.app (𝟙_ C, 𝟙_ C)).hom ≫ (δ.hom ⊗ₘ δ.hom) ≫ (λ_ (𝟙_ D)).hom := by
  dsimp only
  apply (cancel_mono d.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← F.map_comp_assoc, he, F.map_comp, Category.assoc, hr]
  have hn := μ.hom.naturality (Prod.mkHom e.hom e.hom)
  change F.map (e.hom ⊗ₘ e.hom) ≫ (μ.app (U, U)).hom =
    (μ.app (𝟙_ C, 𝟙_ C)).hom ≫ (F.map e.hom ⊗ₘ F.map e.hom) at hn
  rw [reassoc_of% hn, hd]
  simp only [tensorHom_comp_tensorHom_assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

private theorem multiplication_of_left_unit
    {C D : Type*} [Category* C] [MonoidalCategory C]
    [Category* D] [MonoidalCategory D]
    (F : C ⥤ D) (μ : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (ε : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (h : (μ.app (𝟙_ C, 𝟙_ C)).hom ≫ (ε.hom ⊗ₘ 𝟙 _) ≫
      (λ_ (F.obj (𝟙_ C))).hom = F.map (λ_ (𝟙_ C)).hom) :
    F.map (λ_ (𝟙_ C)).hom ≫ ε.hom =
      (μ.app (𝟙_ C, 𝟙_ C)).hom ≫ (ε.hom ⊗ₘ ε.hom) ≫ (λ_ (𝟙_ D)).hom := by
  rw [← h]
  simp only [Category.assoc]
  congr 1
  rw [tensorHom_id, MonoidalCategory.tensorHom_def, Category.assoc, leftUnitor_naturality]
  rfl

-- Specialize the generic multiplication calculation to the coefficient systems.
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- The chosen coherent system unit comparison is the normalized ring-unit pullback.
Source: Stacks 07A4 and 0941, pure-tensor unit calculation.
(blueprint: lem-pur-completed-unit-coherent-system-normalization-system-unit).
The comparison is determined uniquely by the two unitor equations. -/
theorem completedUnit_systemPullbackUnit_normalization {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((pullbackTensorSystemComparison_unit l E f).choose).hom =
      (tensorSystemPullbackUnit l E f).hom := by
  let F := pullbackTensorSequenceDerived l E f
  let μ := pullbackTensorSystemComparison l E f
  let : MonoidalCategory (coefficientSequenceDerived l E Y) :=
    (pullbackTensorCalculus l E Y).systemClosed.monoidal
  let : MonoidalCategory (coefficientSequenceDerived l E X) :=
    (pullbackTensorCalculus l E X).systemClosed.monoidal
  let ε := (pullbackTensorSystemComparison_unit l E f).choose
  let δ := tensorSystemPullbackUnit l E f
  have hε := ((pullbackTensorSystemComparison_unit l E f).choose_spec (𝟙_ _)).1
  have he : F.map (λ_ (𝟙_ (coefficientSequenceDerived l E Y))).hom ≫ ε.hom =
      (μ.app (𝟙_ _, 𝟙_ _)).hom ≫ (ε.hom ⊗ₘ ε.hom) ≫ (λ_ (𝟙_ _)).hom := by
    apply multiplication_of_left_unit F μ ε
    exact hε
  have hd : F.map (λ_ (𝟙_ (coefficientSequenceDerived l E Y))).hom ≫ δ.hom =
      (μ.app (𝟙_ _, 𝟙_ _)).hom ≫ (δ.hom ⊗ₘ δ.hom) ≫ (λ_ (𝟙_ _)).hom :=
    transport_regular_multiplication F μ
      (tensorSystemUnit l E Y) (tensorSystemUnit l E X)
      (regularSystemMultiplication l E Y).hom (regularSystemMultiplication l E X).hom
      (tensorSystemRegularPullback l E f)
      (regularSystemMultiplication_coordinates l E Y)
      (regularSystemMultiplication_coordinates l E X)
      (regularSystemPullback_multiplication l E f)
  apply unit_multiplication_iso_unique
    ((μ.app (𝟙_ _, 𝟙_ _)).inv ≫ F.map (λ_ (𝟙_ _)).hom) ε δ
  · simp only [Category.assoc, he, Iso.inv_hom_id_assoc]
  · simp only [Category.assoc, hd, Iso.inv_hom_id_assoc]

end WeilConjectures.CompletedUnitPullback
