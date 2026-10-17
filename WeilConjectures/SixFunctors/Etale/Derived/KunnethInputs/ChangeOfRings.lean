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
/-- `ModuleCat.tensorRestrictScalarsHom` is bijective: it is the composite of the symmetries and
the inverse of the cancellation `P ⊗_S (S ⊗_R M) ≃ P ⊗_R M`. -/
lemma bijective_tensorRestrictScalarsHom (M : ModuleCat.{u} R) (P : ModuleCat.{u} S) :
    Function.Bijective (tensorRestrictScalarsHom f M P) := by
  letI := f.toAlgebra
  letI : Module R P := Module.compHom P f
  haveI : IsScalarTower R S P := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let e : M ⊗[R] P ≃+ (S ⊗[R] M) ⊗[S] P :=
    ((TensorProduct.comm R M P).toAddEquiv.trans
      (AlgebraTensorModule.cancelBaseChange R S S P M).symm.toAddEquiv).trans
      (TensorProduct.comm S P (S ⊗[R] M)).toAddEquiv
  have key : ∀ x : M ⊗[R] P, tensorRestrictScalarsHom f M P x = e x := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero e).symm
    | tmul m p =>
      rw [tensorRestrictScalarsHom_tmul]
      rfl
    | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ _ hx hy).trans (map_add e x y).symm)
  exact ⟨fun a b hab ↦ e.injective ((key a).symm.trans (hab.trans (key b))),
    fun y ↦ ⟨e.symm y, (key _).trans (e.apply_symm_apply y)⟩⟩

/-- `M ⊗_R P ≅ (S ⊗_R M) ⊗_S P` as `R`-modules, for an `R`-module `M` and an `S`-module `P`,
`m ⊗ p ↦ (1 ⊗ m) ⊗ p`. -/
noncomputable def tensorRestrictScalarsIso (M : ModuleCat.{u} R) (P : ModuleCat.{u} S) :
    M ⊗ (restrictScalars f).obj P ≅ (restrictScalars f).obj ((extendScalars f).obj M ⊗ P) :=
  have : IsIso (tensorRestrictScalarsHom f M P) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_tensorRestrictScalarsHom f M P)
  asIso (tensorRestrictScalarsHom f M P)

end ModuleCat
