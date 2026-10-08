/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Descent for a finite family of flat algebras

Let `A` be a commutative ring, `J` a finite type, `B : J → Type*` a family of commutative
`A`-algebras and `N j` a `B j`-module for every `j`. Suppose given `B j`-linear maps
`θ j k : N j →ₗ[B j] B j ⊗[A] N k` (a "coalgebra" form of descent data) satisfying

* the unit condition: `μ j (θ j j x) = x`, where `μ j : B j ⊗[A] N j → N j` is `b ⊗ₜ n ↦ b • n`;
* the cocycle condition: `(B j ⊗ θ k l) (θ j k x) = (B j ⊗ (n ↦ 1 ⊗ₜ n)) (θ j l x)`.

We define the `A`-submodule `TensorProduct.descentSubmodule θ` of `∀ j, N j` consisting of the
families `n` with `θ j k (n j) = 1 ⊗ₜ n k` for all `j k`, and show that for every `l` such that
`B l` is flat over `A`, the natural map `B l ⊗[A] descentSubmodule θ → N l`,
`b ⊗ₜ n ↦ b • n l`, is bijective (`TensorProduct.bijective_descentLift_of_flat`).

## Main definitions

* `TensorProduct.descentDiff θ`: the map `n ↦ (θ j k (n j) - 1 ⊗ₜ n k)_{j k}`.
* `TensorProduct.descentSubmodule θ`: the kernel of `descentDiff θ`.
* `TensorProduct.descentLift θ l`: the `B l`-linear map `B l ⊗[A] descentSubmodule θ → N l`.
* `TensorProduct.descentEquiv`: the resulting `B l`-linear equivalence when `B l` is flat.
-/

@[expose] public section

open LinearMap

namespace TensorProduct

section Pi

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {P : ι → Type*} [∀ i, AddCommGroup (P i)]
  [∀ i, Module R (P i)]

/-- The `i`-th component of `TensorProduct.piRight` is `lTensor M (proj i)`. -/
lemma piRight_apply_eq_lTensor_proj (x : M ⊗[R] (∀ i, P i)) (i : ι) :
    piRight R R M P x i = (LinearMap.proj i : (∀ i, P i) →ₗ[R] P i).lTensor M x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m p => simp
  | add x y hx hy => simp_all

/-- An element of `M ⊗[R] (∀ i, P i)` (with `ι` finite) vanishes if all its components
`lTensor M (proj i) x` vanish. -/
lemma eq_zero_of_lTensor_proj_eq_zero (x : M ⊗[R] (∀ i, P i))
    (h : ∀ i, (LinearMap.proj i : (∀ i, P i) →ₗ[R] P i).lTensor M x = 0) : x = 0 := by
  apply (piRight R R M P).injective
  ext i
  simp only [piRight_apply_eq_lTensor_proj, h, map_zero]

end Pi

variable {A : Type*} [CommRing A] {J : Type*}
  {B : J → Type*} [∀ j, CommRing (B j)] [∀ j, Algebra A (B j)]
  {N : J → Type*} [∀ j, AddCommGroup (N j)] [∀ j, Module (B j) (N j)] [∀ j, Module A (N j)]
  [∀ j, IsScalarTower A (B j) (N j)]

/-- The `A`-linear map `(∀ j, N j) → ∀ j k, B j ⊗[A] N k` sending `n` to
`θ j k (n j) - 1 ⊗ₜ n k`. Its kernel is the module of descended elements. -/
def descentDiff (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k) :
    (∀ j, N j) →ₗ[A] ∀ j k, B j ⊗[A] N k :=
  LinearMap.pi fun j ↦ LinearMap.pi fun k ↦
    (θ j k).restrictScalars A ∘ₗ LinearMap.proj j -
      (TensorProduct.mk A (B j) (N k) 1) ∘ₗ LinearMap.proj k

/-- The components of `descentDiff θ n` are `θ j k (n j) - 1 ⊗ₜ n k`. -/
@[simp]
lemma descentDiff_apply (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k) (n : ∀ j, N j) (j k : J) :
    descentDiff θ n j k = θ j k (n j) - 1 ⊗ₜ n k :=
  rfl

/-- The `A`-submodule of `∀ j, N j` of families `n` with `θ j k (n j) = 1 ⊗ₜ n k`
for all `j k`. -/
def descentSubmodule (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k) : Submodule A (∀ j, N j) :=
  LinearMap.ker (descentDiff θ)

/-- A family `n` lies in `descentSubmodule θ` iff `θ j k (n j) = 1 ⊗ₜ n k` for all `j k`. -/
lemma mem_descentSubmodule (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k) (n : ∀ j, N j) :
    n ∈ descentSubmodule θ ↔ ∀ j k, θ j k (n j) = 1 ⊗ₜ n k := by
  simp [descentSubmodule, funext_iff, sub_eq_zero]

/-- The `B l`-linear map `B l ⊗[A] descentSubmodule θ → N l`, `b ⊗ₜ n ↦ b • n l`. -/
def descentLift (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k) (l : J) :
    B l ⊗[A] descentSubmodule θ →ₗ[B l] N l :=
  (LinearMap.proj l ∘ₗ (descentSubmodule θ).subtype).liftBaseChange (B l)

/-- The value of `descentLift θ l` on a pure tensor `b ⊗ₜ n` is `b • n l`. -/
@[simp]
lemma descentLift_tmul (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k) (l : J) (b : B l)
    (n : descentSubmodule θ) :
    descentLift θ l (b ⊗ₜ n) = b • (n : ∀ j, N j) l :=
  rfl

/-- `descentLift θ l` factors through `lTensor (B l)` of the inclusion of the descent submodule
followed by `b ⊗ₜ n ↦ b • n l`. -/
lemma descentLift_eq (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k) (l : J)
    (w : B l ⊗[A] descentSubmodule θ) :
    descentLift θ l w = (LinearMap.id : N l →ₗ[A] N l).liftBaseChange (B l)
      ((LinearMap.proj l : (∀ j, N j) →ₗ[A] N l).lTensor (B l)
        ((descentSubmodule θ).subtype.lTensor (B l) w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul b n => simp
  | add x y hx hy => simp_all

/-- For a `B`-linear `θ : N →ₗ[B] P`, applying `B ⊗ θ` and then the action map
`B ⊗[A] P → P` agrees with applying the action map `B ⊗[A] N → N` and then `θ`. -/
lemma liftBaseChange_lTensor_restrictScalars {B N P : Type*} [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P]
    (θ : N →ₗ[B] P) (x : B ⊗[A] N) :
    (LinearMap.id : P →ₗ[A] P).liftBaseChange B ((θ.restrictScalars A).lTensor B x) =
      θ ((LinearMap.id : N →ₗ[A] N).liftBaseChange B x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b n => simp
  | add x y hx hy => simp_all

/-- Applying `b ⊗ₜ n ↦ b ⊗ₜ 1 ⊗ₜ n` and then multiplying the first two factors is the identity
of `B ⊗[A] N`. -/
lemma liftBaseChange_lTensor_mk_one {B N : Type*} [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] (x : B ⊗[A] N) :
    (LinearMap.id : B ⊗[A] N →ₗ[A] B ⊗[A] N).liftBaseChange B
      ((TensorProduct.mk A B N 1).lTensor B x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b n => simp [smul_tmul']
  | add x y hx hy => simp_all

/-- **Descent for a finite family of flat algebras.** Given descent data `θ` satisfying the unit
and cocycle conditions, for every `l` with `B l` flat over `A`, the natural map
`B l ⊗[A] descentSubmodule θ → N l`, `b ⊗ₜ n ↦ b • n l`, is bijective. -/
theorem bijective_descentLift_of_flat (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k)
    (hunit : ∀ j (x : N j), (LinearMap.id : N j →ₗ[A] N j).liftBaseChange (B j) (θ j j x) = x)
    (hcocycle : ∀ j k l (x : N j),
      ((θ k l).restrictScalars A).lTensor (B j) (θ j k x) =
        (TensorProduct.mk A (B k) (N l) 1).lTensor (B j) (θ j l x))
    [Fintype J] [DecidableEq J] (l : J) [Module.Flat A (B l)] :
    Function.Bijective (descentLift θ l) := by
  have hinj : Function.Injective ((descentSubmodule θ).subtype.lTensor (B l)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (descentSubmodule θ).injective_subtype
  have hex : Function.Exact ((descentSubmodule θ).subtype.lTensor (B l))
      ((descentDiff θ).lTensor (B l)) :=
    Module.Flat.lTensor_exact (B l) (LinearMap.exact_subtype_ker_map _)
  have hcomp (z : B l ⊗[A] (∀ j, N j)) (j k : J) :
      (LinearMap.proj k).lTensor (B l)
        ((LinearMap.proj j).lTensor (B l) ((descentDiff θ).lTensor (B l) z)) =
        ((θ j k).restrictScalars A).lTensor (B l) ((LinearMap.proj j).lTensor (B l) z) -
          (TensorProduct.mk A (B j) (N k) 1).lTensor (B l)
            ((LinearMap.proj k).lTensor (B l) z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b n => simp [tmul_sub]
    | add x y hx hy =>
      simp only [map_add, hx, hy]
      abel
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    apply hinj
    rw [map_zero]
    apply eq_zero_of_lTensor_proj_eq_zero
    intro k
    have hlk := hcomp ((descentSubmodule θ).subtype.lTensor (B l) w) l k
    rw [hex.apply_apply_eq_zero, map_zero, map_zero, eq_comm, sub_eq_zero] at hlk
    have := congrArg ((LinearMap.id : B l ⊗[A] N k →ₗ[A] B l ⊗[A] N k).liftBaseChange (B l)) hlk
    rw [liftBaseChange_lTensor_restrictScalars, liftBaseChange_lTensor_mk_one,
      ← descentLift_eq, hw, map_zero] at this
    exact this.symm
  · intro x
    set z := (piRight A A (B l) N).symm (fun j ↦ θ l j x) with hz
    have hzj (j : J) : (LinearMap.proj j : (∀ j, N j) →ₗ[A] N j).lTensor (B l) z = θ l j x := by
      rw [← piRight_apply_eq_lTensor_proj, hz, LinearEquiv.apply_symm_apply]
    have hker : (descentDiff θ).lTensor (B l) z = 0 := by
      apply eq_zero_of_lTensor_proj_eq_zero
      intro j
      apply eq_zero_of_lTensor_proj_eq_zero
      intro k
      rw [hcomp, hzj, hzj, hcocycle, sub_self]
    obtain ⟨w, hw⟩ := (hex z).mp hker
    exact ⟨w, by rw [descentLift_eq, hw, hzj, hunit]⟩

/-- The `B l`-linear equivalence `B l ⊗[A] descentSubmodule θ ≃ₗ[B l] N l` obtained from
`TensorProduct.bijective_descentLift_of_flat`. -/
noncomputable def descentEquiv (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k)
    (hunit : ∀ j (x : N j), (LinearMap.id : N j →ₗ[A] N j).liftBaseChange (B j) (θ j j x) = x)
    (hcocycle : ∀ j k l (x : N j),
      ((θ k l).restrictScalars A).lTensor (B j) (θ j k x) =
        (TensorProduct.mk A (B k) (N l) 1).lTensor (B j) (θ j l x))
    [Fintype J] [DecidableEq J] (l : J) [Module.Flat A (B l)] :
    B l ⊗[A] descentSubmodule θ ≃ₗ[B l] N l :=
  LinearEquiv.ofBijective (descentLift θ l) (bijective_descentLift_of_flat θ hunit hcocycle l)

/-- `descentEquiv` agrees with `descentLift`. -/
@[simp]
lemma descentEquiv_apply (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k)
    (hunit : ∀ j (x : N j), (LinearMap.id : N j →ₗ[A] N j).liftBaseChange (B j) (θ j j x) = x)
    (hcocycle : ∀ j k l (x : N j),
      ((θ k l).restrictScalars A).lTensor (B j) (θ j k x) =
        (TensorProduct.mk A (B k) (N l) 1).lTensor (B j) (θ j l x))
    [Fintype J] [DecidableEq J] (l : J) [Module.Flat A (B l)] (w : B l ⊗[A] descentSubmodule θ) :
    descentEquiv θ hunit hcocycle l w = descentLift θ l w :=
  rfl

/-- The value of `descentEquiv` on a pure tensor `b ⊗ₜ n` is `b • n l`. -/
lemma descentEquiv_tmul (θ : ∀ j k, N j →ₗ[B j] B j ⊗[A] N k)
    (hunit : ∀ j (x : N j), (LinearMap.id : N j →ₗ[A] N j).liftBaseChange (B j) (θ j j x) = x)
    (hcocycle : ∀ j k l (x : N j),
      ((θ k l).restrictScalars A).lTensor (B j) (θ j k x) =
        (TensorProduct.mk A (B k) (N l) 1).lTensor (B j) (θ j l x))
    [Fintype J] [DecidableEq J] (l : J) [Module.Flat A (B l)] (b : B l) (n : descentSubmodule θ) :
    descentEquiv θ hunit hcocycle l (b ⊗ₜ n) = b • (n : ∀ j, N j) l :=
  rfl

end TensorProduct
