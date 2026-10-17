/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-!
# Change of rings for the derived tensor product
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory TensorProduct

open scoped ChangeOfRings

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- The comparison `M ⊗_R P ⟶ (S ⊗_R M) ⊗_S P`, `m ⊗ p ↦ (1 ⊗ m) ⊗ p`, for an `R`-module `M`
and an `S`-module `P`, natural in `P`. -/
noncomputable def tensorRestrictScalarsHom (M : ModuleCat.{u} R) (P : ModuleCat.{u} S) :
    M ⊗ (restrictScalars f).obj P ⟶ (restrictScalars f).obj ((extendScalars f).obj M ⊗ P) :=
  (extendRestrictScalarsAdj f).unit.app M ▷ _ ≫
    Functor.LaxMonoidal.μ (restrictScalars f) ((extendScalars f).obj M) P

set_option backward.isDefEq.respectTransparency false in
lemma tensorRestrictScalarsHom_tmul (M : ModuleCat.{u} R) (P : ModuleCat.{u} S) (m : M)
    (p : P) :
    tensorRestrictScalarsHom f M P (m ⊗ₜ p) = ((1 : S) ⊗ₜ[R, f] m) ⊗ₜ p := by
  simp [tensorRestrictScalarsHom]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse of `ModuleCat.tensorRestrictScalarsHom`: `(s ⊗ m) ⊗ p ↦ m ⊗ s • p`. -/
noncomputable def tensorRestrictScalarsInv (M : ModuleCat.{u} R) (P : ModuleCat.{u} S) :
    (restrictScalars f).obj ((extendScalars f).obj M ⊗ P) ⟶ M ⊗ (restrictScalars f).obj P :=
  letI := f.toAlgebra
  letI : Module R P := Module.compHom P f
  haveI : IsScalarTower R S P := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  ofHom
    { toFun := fun x ↦ TensorProduct.comm R P M
        (AlgebraTensorModule.cancelBaseChange R S S P M (TensorProduct.comm S _ P x))
      map_add' := by intros; simp only [map_add]
      map_smul' := fun r x ↦ by
        have h : ∀ y : P ⊗[R] M, TensorProduct.comm R P M (f r • y) =
            r • TensorProduct.comm R P M y := fun y ↦ by
          induction y using TensorProduct.induction_on with
          | zero => simp
          | tmul p m =>
            rw [TensorProduct.smul_tmul', TensorProduct.comm_tmul, TensorProduct.comm_tmul,
              TensorProduct.tmul_smul]
            rfl
          | add y₁ y₂ h₁ h₂ => simp only [smul_add, map_add, h₁, h₂]
        dsimp
        rw [← h, ← map_smul, ← map_smul]
        rfl }

set_option backward.isDefEq.respectTransparency.types false in
lemma tensorRestrictScalarsInv_tmul_tmul (M : ModuleCat.{u} R) (P : ModuleCat.{u} S) (s : S)
    (m : M) (p : P) :
    tensorRestrictScalarsInv f M P ((s ⊗ₜ[R, f] m) ⊗ₜ p) =
      (m ⊗ₜ (s • p : P) : M ⊗ (restrictScalars f).obj P) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- `M ⊗_R P ≅ (S ⊗_R M) ⊗_S P` as `R`-modules, for an `R`-module `M` and an `S`-module `P`. -/
noncomputable def tensorRestrictScalarsIso (M : ModuleCat.{u} R) (P : ModuleCat.{u} S) :
    M ⊗ (restrictScalars f).obj P ≅ (restrictScalars f).obj ((extendScalars f).obj M ⊗ P) where
  hom := tensorRestrictScalarsHom f M P
  inv := tensorRestrictScalarsInv f M P
  hom_inv_id := by
    ext m p
    dsimp
    rw [tensorRestrictScalarsHom_tmul, tensorRestrictScalarsInv_tmul_tmul, one_smul]
  inv_hom_id := by
    ext x
    dsimp
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul y p =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul s m =>
        rw [tensorRestrictScalarsInv_tmul_tmul, tensorRestrictScalarsHom_tmul,
          TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul,
          mul_one]
      | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
    | add x₁ x₂ h₁ h₂ => simp only [map_add, h₁, h₂]

end ModuleCat
