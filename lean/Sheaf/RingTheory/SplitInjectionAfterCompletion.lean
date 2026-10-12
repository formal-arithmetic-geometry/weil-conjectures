/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Operations
import Sheaf.LinearAlgebra.SplitExtensionFreePresentation

/-!
# Split injections detected modulo arbitrarily high ideal powers

Source: Stacks Project, Algebra, Lemma 10.74.1, Tag 02HO
(blueprint: lem-weil-pbc-split-injection-after-completion).
-/

@[expose] public section

universe u v w

/-- Source: Stacks Project, Algebra, Lemma 10.74.1, Tag 02HO.
(blueprint: lem-weil-pbc-split-injection-after-completion)
A map of finite modules over a Noetherian ring splits if its reductions modulo arbitrarily
high powers of an ideal in the Jacobson radical split. The quotient splitting is expressed
by composing with the quotient projection; this is equivalent to a left inverse of the
induced quotient map, since the projection from `N` is surjective.

Proof:
1. An element of the kernel belongs to `J^k N` for arbitrarily large `k`, hence for every `k`.
   Krull intersection (lem-weil-pbc-krull-intersection-jacobson) makes the kernel zero.
2. Choose a finite free presentation `F₁ → F₀ → Q → 0` of the cokernel `Q = M/u(N)`.
   The kernel of the finite free surjection is finite by
   lem-weil-pbc-noetherian-submodule-finite. Lift `F₀ → Q` to `α : F₀ → M`; injectivity
   gives `β : F₁ → N` with `u β = α d₁`.
3. For each splitting exponent, compose the quotient retraction with `qM α` and lift this
   map from the free module `F₀` to `γk : F₀ → N`. Then `β - γk d₁` lands in `J^k N`.
4. In `H = Hom(F₁,N)`, finite freeness identifies this condition with membership in
   `J^k H`. The class of `β` in the finite cokernel of precomposition by `d₁` therefore
   belongs to every ideal power. Apply lem-weil-pbc-krull-intersection-jacobson again to
   obtain `β = γ d₁` for some `γ : F₀ → N`.
5. The criterion lem-weil-pbc-split-extension-free-presentation now gives the required
   retraction of `u`. -/
theorem LinearMap.exists_leftInverse_of_split_mod_pow
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N] [Module.Finite A N]
    {M : Type w} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (J : Ideal A) (hJ : J ≤ (⊥ : Ideal A).jacobson) (u : N →ₗ[A] M)
    (hsplit : ∀ b : ℕ, ∃ k : ℕ, b ≤ k ∧
      ∃ vk : (M ⧸ (J ^ k • (⊤ : Submodule A M))) →ₗ[A]
          (N ⧸ (J ^ k • (⊤ : Submodule A N))),
        vk.comp (((J ^ k • (⊤ : Submodule A M)).mkQ).comp u) =
          (J ^ k • (⊤ : Submodule A N)).mkQ) :
    ∃ v : M →ₗ[A] N, v.comp u = LinearMap.id := by
  sorry
