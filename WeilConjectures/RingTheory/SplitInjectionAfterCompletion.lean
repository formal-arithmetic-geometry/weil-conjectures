/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Operations
import WeilConjectures.RingTheory.FiniteRelationSplittingData
import WeilConjectures.RingTheory.RelationFactorsOfApproximation
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Filtration

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
  have hu : Function.Injective u := by
    intro x y hxy
    have hz : u (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hzall : x - y ∈ (⨅ k : ℕ, J ^ k • (⊤ : Submodule A N)) := by
      rw [Submodule.mem_iInf]
      intro b
      obtain ⟨k, hk, vk, hvk⟩ := hsplit b
      have hzero : (J ^ k • (⊤ : Submodule A N)).mkQ (x - y) = 0 := by
        rw [← hvk]
        simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
        rw [hz]
        exact map_zero vk
      have hzk : x - y ∈ J ^ k • (⊤ : Submodule A N) :=
        (Submodule.Quotient.mk_eq_zero _).mp hzero
      exact (Submodule.smul_mono (Ideal.pow_le_pow_right hk) le_top) hzk
    have hbot := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := N) J hJ
    rw [hbot] at hzall
    exact sub_eq_zero.mp hzall
  obtain ⟨a, b, d, α, β, hβ, hdescend⟩ :=
    LinearMap.exists_finite_relation_splitting_data u hu
  have happrox : ∀ c : ℕ, ∃ k : ℕ, c ≤ k ∧
      ∃ γ : (Fin a → A) →ₗ[A] N,
        ∀ x, (β - γ.comp d) x ∈ J ^ k • (⊤ : Submodule A N) := by
    intro c
    obtain ⟨k, hk, vk, hvk⟩ := hsplit c
    obtain ⟨γ, hγ⟩ := Module.projective_lifting_property
      (J ^ k • (⊤ : Submodule A N)).mkQ
      (vk.comp ((J ^ k • (⊤ : Submodule A M)).mkQ.comp α))
      (Submodule.mkQ_surjective _)
    refine ⟨k, hk, γ, fun x ↦ (Submodule.Quotient.mk_eq_zero _).mp ?_⟩
    change (J ^ k • (⊤ : Submodule A N)).mkQ ((β - γ.comp d) x) = 0
    rw [LinearMap.sub_apply, map_sub, LinearMap.comp_apply]
    have hrel : u (β x) = α (d x) := DFunLike.congr_fun hβ x
    have hsplitx := DFunLike.congr_fun hvk (β x)
    have hliftx := DFunLike.congr_fun hγ (d x)
    simp only [LinearMap.comp_apply] at hsplitx hliftx
    rw [hliftx, ← hrel, hsplitx, sub_self]
  obtain ⟨γ, hγ⟩ := LinearMap.exists_relation_factor_of_approximation J hJ d β happrox
  exact hdescend γ hγ
