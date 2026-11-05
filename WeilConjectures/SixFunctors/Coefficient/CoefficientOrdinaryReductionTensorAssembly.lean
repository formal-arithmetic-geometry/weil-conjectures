/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels

/-! # Assembling maps of coefficient systems from their finite evaluations

Source: Stacks Project, Tags 03CZ and 0941.

A family of maps between the finite evaluations of two modules on the ringed sequence
site, compatible with the strict transition maps, assembles to a unique map of modules
on the sequence site. Maps of modules on the sequence site are determined by their
finite evaluations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
universe t u r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.OrdinaryReductionTensor
namespace GeneralAssembly
universe c v
variable {T : Type c} [Category.{v} T] (J : GrothendieckTopology T)
    (R : Sheaf (coefficientSequenceTopology J) RingCat.{r})
    (S : ℕ → Sheaf J RingCat.{r})

variable (φ : ∀ n : ℕ, S n ≅
  ((Prod.sectR n T).sheafPushforwardContinuous RingCat.{r} J
    (coefficientSequenceTopology J)).obj R)

variable (κ : ∀ {m n : ℕ}, n ≤ m → (S m ⟶ S n))
    (δ : ∀ {m n : ℕ} (h : n ≤ m), (SheafOfModules.pushforward.{r} (φ m).hom) ⟶
      (SheafOfModules.pushforward.{r} (φ n).hom) ⋙ SheafOfModules.restrictScalars (κ h))
    (hδ : ∀ {m n : ℕ} (h : n ≤ m) (M : SheafOfModules.{r} R) (V : Tᵒᵖ),
      HEq (fun x ↦ ((δ h).app M).val.app V x)
        (fun x : M.val.obj (op (m, V.unop)) ↦
          M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x))
    {M N : SheafOfModules.{r} R}
    (d : ∀ n : ℕ, (SheafOfModules.pushforward.{r} (φ n).hom).obj M ⟶
      (SheafOfModules.pushforward.{r} (φ n).hom).obj N)
    (ht : ∀ {m n : ℕ} (h : n ≤ m),
      (δ h).app M ≫ (SheafOfModules.restrictScalars (κ h)).map (d n) =
        d m ≫ (δ h).app N)

/-- The sectionwise components of the assembled map.
Source: Stacks 03CZ, 0941. -/
@[irreducible] def assemble_app (V : (ℕ × T)ᵒᵖ) :
    M.val.obj V ⟶ N.val.obj V :=
  undoRestriction
    (((CategoryTheory.evaluation Tᵒᵖ RingCat.{r}).obj (op V.unop.2)).mapIso
      ((sheafToPresheaf J RingCat.{r}).mapIso (φ V.unop.1)))
    ((d V.unop.1).val.app (op V.unop.2))

include ht hδ in
/-- The map of sequence-site modules assembled from compatible levelwise maps.
Source: Stacks 03CZ, 0941. -/
@[irreducible] def assemble : M ⟶ N where
  val := {
    app := assemble_app J R S φ d
    naturality := by
      intro V Z f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change assemble_app J R S φ d Z (M.val.map f x) =
        N.val.map f (assemble_app J R S φ d V x)
      let a : V ⟶ op (V.unop.1, Z.unop.2) :=
        (Prod.mkHom (𝟙 V.unop.1) f.unop.2).op
      let b : op (V.unop.1, Z.unop.2) ⟶ Z :=
        (Prod.mkHom f.unop.1 (𝟙 Z.unop.2)).op
      have hab : f = a ≫ b := by
        apply Quiver.Hom.unop_inj
        apply Prod.hom_ext <;> simp [a, b]
      have hv : assemble_app J R S φ d (op (V.unop.1, Z.unop.2)) (M.val.map a x) =
          N.val.map a (assemble_app J R S φ d V x) := by
        simp only [assemble_app_apply]
        exact PresheafOfModules.naturality_apply (d V.unop.1).val f.unop.2.op x
      rw [hab, M.val.map_comp_apply, N.val.map_comp_apply, ← hv]
      exact (horizontal_natural J R S φ κ δ hδ d ht (leOfHom f.unop.1)
        (op Z.unop.2) (M.val.map a x)).symm }

end GeneralAssembly

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

section Assembly
variable {M N : coefficientSequenceModules l E W}
  (d : ∀ n : ℕ, (coefficientSequenceEvaluation l E W n).obj M ⟶
    (coefficientSequenceEvaluation l E W n).obj N)
  (ht : ∀ {m n : ℕ} (h : n ≤ m),
    (coefficientSequenceTransition l E W h).app M ≫
      (normalizedDVRModuleRes l E W h).map (d n) =
    d m ≫ (coefficientSequenceTransition l E W h).app N)

include d ht in
/-- The map of sequence-site modules assembled from compatible finite evaluations.
Source: Stacks 03CZ, 0941. -/
@[irreducible] def coefficientSequenceAssemble : M ⟶ N :=
  GeneralAssembly.assemble (Scheme.ProEt.topology W) (coefficientRing l E W)
    (integralCoefficientSheaf l E W)
    (fun n ↦ eqToIso (coefficientSequenceEvaluationRing_eq l E W n).symm)
    (fun {_ _} h ↦ normalizedDVRQuotient l E W h)
    (fun {_ _} h ↦ coefficientSequenceTransition l E W h)
    (fun {_ _} h M V ↦ transition_functions l E W h M V) d ht

end Assembly
end WeilConjectures.OrdinaryReductionTensor
