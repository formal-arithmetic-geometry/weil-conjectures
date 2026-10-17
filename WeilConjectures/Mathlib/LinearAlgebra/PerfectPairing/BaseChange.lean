/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Base change of perfect pairings

Let `p : M × N ⟶ R` be a pairing of `R`-modules with `N` finite free, and `A` an `R`-algebra.
The base change `p_A : (A ⊗_R M) × (A ⊗_R N) ⟶ A` is `(a ⊗ m, a' ⊗ n) ↦ a a' p(m, n)`. If `M`
and `N` are finite free and `p` is perfect, so is `p_A`. For `A = R/I` this says that a perfect
pairing of finite free modules reduces to perfect pairings modulo every ideal.

## Main definitions

- `LinearMap.pairingBaseChange`: the base change `p_A` of a pairing `p`.

## Main statements

- `LinearMap.IsPerfPair.pairingBaseChange`: the base change of a perfect pairing of finite free
  modules is perfect.
-/

@[expose] public section

open Module TensorProduct

namespace LinearMap

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (A : Type*) [CommRing A] [Algebra R A]

/-- The base change `(A ⊗_R M) × (A ⊗_R N) ⟶ A`, `(a ⊗ m, a' ⊗ n) ↦ a a' p(m, n)`, of a pairing
`p : M × N ⟶ R` with `N` finite free: the base change `A ⊗_R M ⟶ A ⊗_R N^∨` of
`p : M ⟶ N^∨` followed by `A ⊗_R N^∨ ≅ (A ⊗_R N)^∨`. -/
noncomputable def pairingBaseChange [Free R N] [Module.Finite R N] (p : M →ₗ[R] N →ₗ[R] R) :
    A ⊗[R] M →ₗ[A] A ⊗[R] N →ₗ[A] A :=
  (TensorProduct.isBaseChange R N A).toDualBaseChange.toLinearMap ∘ₗ p.baseChange A

@[simp]
lemma pairingBaseChange_tmul_tmul [Free R N] [Module.Finite R N] (p : M →ₗ[R] N →ₗ[R] R)
    (a a' : A) (m : M) (n : N) :
    pairingBaseChange A p (a ⊗ₜ m) (a' ⊗ₜ n) = a * a' * algebraMap R A (p m n) := by
  have h := (TensorProduct.isBaseChange R N A).toDualBaseChange_tmul a (p m) n
  rw [TensorProduct.mk_apply] at h
  rw [pairingBaseChange, coe_comp, Function.comp_apply, baseChange_tmul, LinearEquiv.coe_coe,
    ← mul_one a', ← smul_eq_mul, ← smul_tmul', map_smul, h, smul_eq_mul]
  ring

/-- The base change of the transpose of a pairing is the transpose of its base change. -/
lemma pairingBaseChange_flip [Free R M] [Module.Finite R M] [Free R N] [Module.Finite R N]
    (p : M →ₗ[R] N →ₗ[R] R) :
    (pairingBaseChange A p).flip = pairingBaseChange A p.flip := by
  refine TensorProduct.AlgebraTensorModule.ext fun a' n ↦ ?_
  refine TensorProduct.AlgebraTensorModule.ext fun a m ↦ ?_
  rw [flip_apply, pairingBaseChange_tmul_tmul, pairingBaseChange_tmul_tmul, flip_apply,
    mul_comm a a']

/-- The base change of a pairing `p : M × N ⟶ R` with `p : M ⟶ N^∨` bijective is bijective as a
map `A ⊗_R M ⟶ (A ⊗_R N)^∨`, for `N` finite free. -/
lemma bijective_pairingBaseChange [Free R N] [Module.Finite R N] (p : M →ₗ[R] N →ₗ[R] R)
    (hp : Function.Bijective p) : Function.Bijective (pairingBaseChange A p) := by
  rw [pairingBaseChange, coe_comp]
  refine (TensorProduct.isBaseChange R N A).toDualBaseChange.bijective.comp ?_
  obtain ⟨e, rfl⟩ : ∃ e : M ≃ₗ[R] (N →ₗ[R] R), e.toLinearMap = p :=
    ⟨.ofBijective p hp, LinearMap.ext fun _ ↦ rfl⟩
  rw [← LinearEquiv.coe_baseChange, LinearEquiv.coe_coe]
  exact (e.baseChange R A M _).bijective

/-- **The base change of a perfect pairing of finite free modules is perfect.** In particular,
for an ideal `I` of `R`, a perfect pairing `M × N ⟶ R` of finite free `R`-modules reduces to a
perfect pairing `M/IM × N/IN ⟶ R/I` (`A = R/I`). -/
instance IsPerfPair.pairingBaseChange [Free R M] [Module.Finite R M] [Free R N]
    [Module.Finite R N] (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair] :
    (pairingBaseChange A p).IsPerfPair where
  bijective_left := bijective_pairingBaseChange A p (IsPerfPair.bijective_left p)
  bijective_right := by
    rw [pairingBaseChange_flip]
    exact bijective_pairingBaseChange A p.flip (IsPerfPair.bijective_right p)

end LinearMap
