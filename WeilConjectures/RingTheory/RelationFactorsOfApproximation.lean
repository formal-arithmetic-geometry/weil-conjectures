/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.Filtration

/-!
# Relation maps approximated by factorizations actually factor

Source: Stacks Project, Algebra, proof of Tag 02HO, lines 18186-18202.
-/

@[expose] public section

universe u v

/-- Source: Stacks Project, Algebra, proof of Tag 02HO, lines 18186-18202.
(blueprint: lem-weil-pbc-relation-factors-of-approximation)

Proof: let `H = Hom(A^b,N)` and let `D` be the image of the linear map
`Hom(A^a,N) → H` given by precomposition with `d`. Evaluation on the standard
basis identifies `H` with `N^b`, so it is finite. Under that identification, a map
with image in `J^k N` belongs to `J^k H`: express each of its finitely many
coordinates as a finite sum of ideal multiples, and place these sums into the
corresponding coordinate. The reverse inclusion follows by evaluating ideal multiples.
In the finite quotient `C = H/D`, the hypothesis says the class of `β` belongs
to `J^k C` for arbitrarily large `k`. Ideal powers decrease, so the class belongs
to every power. Krull intersection for a Jacobson-radical ideal makes this class
zero. Thus `β` belongs to `D`, giving the required `γ`.
The assertion also includes zero free ranks, the zero module, and the zero ideal;
the same quotient argument applies in each case. -/
theorem LinearMap.exists_relation_factor_of_approximation
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (J : Ideal A) (hJ : J ≤ (⊥ : Ideal A).jacobson)
    {a b : ℕ} (d : (Fin b → A) →ₗ[A] (Fin a → A))
    (β : (Fin b → A) →ₗ[A] N)
    (happrox : ∀ c : ℕ, ∃ k : ℕ, c ≤ k ∧
      ∃ γ : (Fin a → A) →ₗ[A] N,
        ∀ x, (β - γ.comp d) x ∈ J ^ k • (⊤ : Submodule A N)) :
    ∃ γ : (Fin a → A) →ₗ[A] N, β = γ.comp d := by
  classical
  let H := (Fin b → A) →ₗ[A] N
  let pre : ((Fin a → A) →ₗ[A] N) →ₗ[A] H := LinearMap.lcomp A N d
  let D := LinearMap.range pre
  let q := D.mkQ
  have hmem (I : Ideal A) (f : H) (hf : ∀ x, f x ∈ I • (⊤ : Submodule A N)) :
      f ∈ I • (⊤ : Submodule A H) := by
    let B := Pi.basisFun A (Fin b)
    let ins (i : Fin b) : N →ₗ[A] H :=
      (B.constr A).toLinearMap.comp (LinearMap.single A (fun _ : Fin b ↦ N) i)
    have heq : f = ∑ i : Fin b, ins i (f (B i)) := by
      apply B.ext
      intro j
      change f (B j) = (∑ i : Fin b, ins i (f (B i))) (B j)
      rw [LinearMap.sum_apply]
      change f (B j) = ∑ i : Fin b, B.constr A (Pi.single i (f (B i))) (B j)
      simp only [Module.Basis.constr_basis]
      simp
    rw [heq]
    apply Submodule.sum_mem
    intro i _
    exact (Submodule.smul_top_le_comap_smul_top I (ins i)) (hf (B i))
  have hclass : q β ∈ ⨅ k : ℕ, J ^ k • (⊤ : Submodule A (H ⧸ D)) := by
    rw [Submodule.mem_iInf]
    intro c
    obtain ⟨k, hk, γ, hγ⟩ := happrox c
    have hdiff := hmem (J ^ k) (β - γ.comp d) hγ
    have hqdiff : q (β - γ.comp d) ∈ J ^ k • (⊤ : Submodule A (H ⧸ D)) :=
      (Submodule.smul_top_le_comap_smul_top (J ^ k) q) hdiff
    have hzero : q (γ.comp d) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero D).mpr
      exact ⟨γ, rfl⟩
    rw [map_sub, hzero, sub_zero] at hqdiff
    exact (Submodule.smul_mono (Ideal.pow_le_pow_right hk) le_top) hqdiff
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := H ⧸ D) J hJ
  rw [hbot] at hclass
  have hzero : q β = 0 := hclass
  have hrange : β ∈ D := (Submodule.Quotient.mk_eq_zero D).mp hzero
  obtain ⟨γ, hγ⟩ := hrange
  exact ⟨γ, hγ.symm⟩
