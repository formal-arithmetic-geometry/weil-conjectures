/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.CategoryTheory.ExactSectionsDerivedCup
public import WeilConjectures.CategoryTheory.Preadditive.CoyonedaSectionsExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! Ordinary normalized tensorator for exact point sections.
Source: Stacks 07A4 and 03EL, ordinary pure-section tensor construction.
(blueprint: lem-pod-condensed-point-tensor-data-exists)

The construction sends pure sections to the sheaf tensor after the inverse
left-unitor. Its additivity and balancing extend the map to the module tensor;
this is the ordinary part of the normalized point tensor data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings CategoryTheory.Obj

section

variable {D : Type v} [Category.{w} D] [Preadditive D] [MonoidalCategory D]
  [MonoidalPreadditive D] {A : Type w} [CommRing A]
  (c : A →+* (End (𝟙_ D))ᵐᵒᵖ)

omit [MonoidalPreadditive D] in
private theorem sectionPair_smul_left (M N : D) (a : A)
    (x : 𝟙_ D ⟶ M) (y : 𝟙_ D ⟶ N) :
    (λ_ (𝟙_ D)).inv ≫ (((c a).unop ≫ x) ⊗ₘ y) =
      (c a).unop ≫ (λ_ (𝟙_ D)).inv ≫ (x ⊗ₘ y) := by
  conv_lhs => rw [← Category.id_comp y, ← tensorHom_comp_tensorHom]
  rw [tensorHom_id, unitors_inv_equal, ← rightUnitor_inv_naturality_assoc]

omit [MonoidalPreadditive D] in
private theorem sectionPair_smul_right (M N : D) (a : A)
    (x : 𝟙_ D ⟶ M) (y : 𝟙_ D ⟶ N) :
    (λ_ (𝟙_ D)).inv ≫ (x ⊗ₘ ((c a).unop ≫ y)) =
      (c a).unop ≫ (λ_ (𝟙_ D)).inv ≫ (x ⊗ₘ y) := by
  conv_lhs => rw [← Category.id_comp x, ← tensorHom_comp_tensorHom]
  rw [id_tensorHom, ← leftUnitor_inv_naturality_assoc]

private def sectionTensor (M N : D) :
    (coyonedaSections c).obj M ⊗ (coyonedaSections c).obj N ⟶
      (coyonedaSections c).obj (M ⊗ N) :=
  ModuleCat.MonoidalCategory.tensorLift
    (M₁ := (coyonedaSections c).obj M) (M₂ := (coyonedaSections c).obj N)
    (M₃ := (coyonedaSections c).obj (M ⊗ N))
    (fun x y ↦ (λ_ (𝟙_ D)).inv ≫ (x ⊗ₘ y))
    (by
      intro x x' y
      change (λ_ (𝟙_ D)).inv ≫ ((x + x' : 𝟙_ D ⟶ M) ⊗ₘ y) = _
      rw [MonoidalPreadditive.add_tensor, Preadditive.comp_add])
    (sectionPair_smul_left c M N)
    (by
      intro x y y'
      change (λ_ (𝟙_ D)).inv ≫ (x ⊗ₘ (y + y' : 𝟙_ D ⟶ N)) = _
      rw [MonoidalPreadditive.tensor_add, Preadditive.comp_add])
    (sectionPair_smul_right c M N)

private theorem sectionTensor_tmul (M N : D)
    (x : (coyonedaSections c).obj M) (y : (coyonedaSections c).obj N) :
    (sectionTensor c M N).hom (x ⊗ₜ[A] y) =
      (λ_ (𝟙_ D)).inv ≫ (x ⊗ₘ y) := rfl

omit [MonoidalPreadditive D] in
private theorem sectionMap_apply {M N : D} (f : M ⟶ N)
    (x : (coyonedaSections c).obj M) :
    ((coyonedaSections c).map f).hom x = x ≫ f := rfl

private def sectionUnit : 𝟙_ (ModuleCat A) ⟶ (coyonedaSections c).obj (𝟙_ D) :=
  ModuleCat.ofHom (X := 𝟙_ (ModuleCat A)) (Y := (coyonedaSections c).obj (𝟙_ D))
    { toFun := fun a ↦ (c a).unop
      map_add' := by intro a b; simp
      map_smul' := by
        intro a b
        change (c (a * b)).unop = (c a).unop ≫ (c b).unop
        simp [End.mul_def] }

omit [Preadditive D] [MonoidalPreadditive D] in
private theorem sectionPair_assoc (M N P : D)
    (x : 𝟙_ D ⟶ M) (y : 𝟙_ D ⟶ N) (z : 𝟙_ D ⟶ P) :
    (λ_ (𝟙_ D)).inv ≫
        (((λ_ (𝟙_ D)).inv ≫ (x ⊗ₘ y)) ⊗ₘ z) ≫ (α_ M N P).hom =
      (λ_ (𝟙_ D)).inv ≫ (x ⊗ₘ ((λ_ (𝟙_ D)).inv ≫ (y ⊗ₘ z))) := by
  simp only [Iso.cancel_iso_inv_left]
  conv_lhs =>
    rw [← Category.id_comp z, ← tensorHom_comp_tensorHom, Category.assoc,
      associator_naturality, ← Category.assoc, unitors_inv_equal,
      tensorHom_id, triangle_assoc_comp_right_inv]
  conv_rhs => rw [← Category.id_comp x, ← tensorHom_comp_tensorHom]
  simp

@[instance_reducible]
private def sectionsLax : (coyonedaSections c).LaxMonoidal where
  ε := sectionUnit c
  «μ» := sectionTensor c
  μ_natural_left := by
    intro M M' f N
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    change (λ_ (𝟙_ D)).inv ≫ ((x ≫ f) ⊗ₘ y) =
      ((λ_ (𝟙_ D)).inv ≫ (x ⊗ₘ y)) ≫ (f ▷ N)
    conv_lhs =>
      rw [← Category.comp_id y, ← tensorHom_comp_tensorHom, tensorHom_id]
    rw [Category.assoc]
  μ_natural_right := by
    intro M M' N f
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    change (λ_ (𝟙_ D)).inv ≫ (x ⊗ₘ (y ≫ f)) =
      ((λ_ (𝟙_ D)).inv ≫ (x ⊗ₘ y)) ≫ (N ◁ f)
    conv_lhs =>
      rw [← Category.comp_id x, ← tensorHom_comp_tensorHom, id_tensorHom]
    rw [Category.assoc]
  associativity := by
    intro M N P
    apply ModuleCat.MonoidalCategory.tensor_ext₃'
    intro x y z
    simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
      ModuleCat.MonoidalCategory.associator_hom_apply, sectionTensor_tmul]
    have ht := ModuleCat.MonoidalCategory.whiskerLeft_apply
      ((coyonedaSections c).obj M) (sectionTensor c N P) x (y ⊗ₜ[A] z)
    rw [ht, sectionTensor_tmul, sectionTensor_tmul]
    rw [sectionMap_apply]
    simpa only [Category.assoc] using sectionPair_assoc M N P x y z
  left_unitality := by
    intro M
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a x
    change (c a).unop ≫ x =
      ((λ_ (𝟙_ D)).inv ≫ ((c a).unop ⊗ₘ x)) ≫ (λ_ M).hom
    rw [MonoidalCategory.tensorHom_def, Category.assoc, Category.assoc,
      leftUnitor_naturality, unitors_inv_equal, ← rightUnitor_inv_naturality_assoc]
    simp [← unitors_inv_equal]
  right_unitality := by
    intro M
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x a
    change (c a).unop ≫ x =
      ((λ_ (𝟙_ D)).inv ≫ (x ⊗ₘ (c a).unop)) ≫ (ρ_ M).hom
    rw [tensorHom_def', Category.assoc, Category.assoc, rightUnitor_naturality,
      ← leftUnitor_inv_naturality_assoc]
    simp [unitors_inv_equal]

end

namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
  [PreservesFiniteLimits (condensedRingCoefficientSections Λ (Spec (.of k)))]
  [PreservesFiniteColimits (condensedRingCoefficientSections Λ (Spec (.of k)))]

set_option linter.unusedSectionVars false in
/-- The ordinary normalized tensorator exists before chain and localization data.
Source: Stacks 07A4 and 03EL, ordinary pure-section tensor construction.
(blueprint: lem-pod-condensed-point-tensor-ordinary-exists)
Proof in words: a section is a map from the regular module; send `x ⊗ y` to
`(λ_ _).inv ≫ (x ⊗ₘ y)`. This is additive and `Γ Λ`-balanced in each variable, so it
extends to the module tensor product; the unit is the regular section, and naturality,
associativity and the unit laws follow from those of the sheaf tensor and its unitors. -/
theorem ordinaryTensorator_exists :
    ∃ m : (condensedRingCoefficientSections Λ (Spec (.of k))).LaxMonoidal,
      ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of k))))
        (x : (condensedRingCoefficientSections Λ (Spec (.of k))).obj M)
        (y : (condensedRingCoefficientSections Λ (Spec (.of k))).obj N),
        (m.μ M N).hom (x ⊗ₜ[Γ Λ] y) = (λ_ _).inv ≫ (x ⊗ₘ y) := by
  refine ⟨sectionsLax _, ?_⟩
  intro M N x y
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint
