/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Degreewise split free resolutions of a short exact sequence

Source: Stacks Project, Algebra, proof of Tag 065P
(blueprint: lem-weil-pbc-free-resolution-ses-split).
-/

@[expose] public section

universe u v₁ v₂ v₃

namespace Module

/-- A short exact sequence of modules admits compatible free resolutions with split rows in
every degree. Source: Stacks Project, Algebra, proof of Tag 065P; Derived Categories,
Tag 064C (blueprint: lem-weil-pbc-free-resolution-ses-split).

Proof plan:
1. For a short exact sequence A → A' → A'', choose generating families of A and A'' and
   lifts in A' of the latter. Take free modules P and P'' on these families and P' = P ⊕ P''.
   The generator maps give compatible surjections onto A, A', A''. Inclusion, projection,
   retraction and section satisfy the four splitting identities. Apply the snake lemma
   (lem-weil-pbc-snake-lemma-modules) to obtain a short exact sequence of kernels;
   surjectivity makes the cokernels zero (def-weil-pbc-exact-sequence).
2. Starting from the given sequence, repeat Step 1 on these kernels. At degree n take
   the resulting free modules (def-weil-pbc-free-module); define the next differential
   as the surjection onto the kernel followed by its inclusion. The initial surjections
   are the augmentations.
3. Each augmentation is surjective. Each differential has image equal to the preceding
   kernel, so the augmented complexes are exact. Compatibility of the kernel inclusions
   and surjections makes α and β chain maps and gives both augmentation squares. The four
   splitting identities hold by construction in every degree, hence all rows are split
   exact (def-weil-pbc-exact-sequence).

As in `Module.exists_finite_free_resolution`, the terms are a family `F : ℕ → Type _` and
`d i : F (i + 1) →ₗ[R] F i` is the node's `d_{i+1}`; exactness of the augmented complex is
surjectivity of `ε` and the kernel-image equalities (which imply `d ∘ d = 0`). Short
exactness of the given sequence is injectivity, `Function.Exact` and surjectivity, the
module form of def-weil-pbc-exact-sequence. The maps `π n` and `s n` are families of linear
maps, not chain maps. The free terms live in `Type (max u v₁ v₂ v₃)`, which holds free
modules on generating sets of all three modules. -/
theorem exists_free_resolution_ses_split
    (R : Type u) [CommRing R]
    {Q : Type v₁} [AddCommGroup Q] [Module R Q]
    {Q' : Type v₂} [AddCommGroup Q'] [Module R Q']
    {Q'' : Type v₃} [AddCommGroup Q''] [Module R Q'']
    (u : Q →ₗ[R] Q') (v : Q' →ₗ[R] Q'')
    (hu : Function.Injective u) (huv : Function.Exact u v) (hv : Function.Surjective v) :
    ∃ (F F' F'' : ℕ → Type (max u v₁ v₂ v₃))
      (_ : ∀ n, AddCommGroup (F n)) (_ : ∀ n, Module R (F n))
      (_ : ∀ n, AddCommGroup (F' n)) (_ : ∀ n, Module R (F' n))
      (_ : ∀ n, AddCommGroup (F'' n)) (_ : ∀ n, Module R (F'' n))
      (d : ∀ i : ℕ, F (i + 1) →ₗ[R] F i) (d' : ∀ i : ℕ, F' (i + 1) →ₗ[R] F' i)
      (d'' : ∀ i : ℕ, F'' (i + 1) →ₗ[R] F'' i)
      (ε : F 0 →ₗ[R] Q) (ε' : F' 0 →ₗ[R] Q') (ε'' : F'' 0 →ₗ[R] Q'')
      (α : ∀ n : ℕ, F n →ₗ[R] F' n) (β : ∀ n : ℕ, F' n →ₗ[R] F'' n)
      (π : ∀ n : ℕ, F' n →ₗ[R] F n) (s : ∀ n : ℕ, F'' n →ₗ[R] F' n),
      (∀ n : ℕ, Module.Free R (F n) ∧ Module.Free R (F' n) ∧ Module.Free R (F'' n)) ∧
      (Function.Surjective ε ∧ LinearMap.ker ε = LinearMap.range (d 0) ∧
        ∀ i : ℕ, LinearMap.ker (d i) = LinearMap.range (d (i + 1))) ∧
      (Function.Surjective ε' ∧ LinearMap.ker ε' = LinearMap.range (d' 0) ∧
        ∀ i : ℕ, LinearMap.ker (d' i) = LinearMap.range (d' (i + 1))) ∧
      (Function.Surjective ε'' ∧ LinearMap.ker ε'' = LinearMap.range (d'' 0) ∧
        ∀ i : ℕ, LinearMap.ker (d'' i) = LinearMap.range (d'' (i + 1))) ∧
      (∀ i : ℕ, d' i ∘ₗ α (i + 1) = α i ∘ₗ d i) ∧
      (∀ i : ℕ, d'' i ∘ₗ β (i + 1) = β i ∘ₗ d' i) ∧
      ε' ∘ₗ α 0 = u ∘ₗ ε ∧ ε'' ∘ₗ β 0 = v ∘ₗ ε' ∧
      ∀ n : ℕ, β n ∘ₗ α n = 0 ∧ π n ∘ₗ α n = LinearMap.id ∧
        β n ∘ₗ s n = LinearMap.id ∧ α n ∘ₗ π n + s n ∘ₗ β n = LinearMap.id := by
  sorry

end Module
