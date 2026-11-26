/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import WeilConjectures.RingTheory.FiniteGradedModuleLowerBound
import WeilConjectures.RingTheory.GradedQuotientSpanDescent

/-!
# Graded Nakayama generation over the projective-line polynomial ring

Graded Nakayama lemma for finite graded modules over `k[x₀,x₁]`: homogeneous lifts of generators
modulo the irrelevant ideal `(x₀,x₁)` generate the module
(`MvPolynomial.graded_nakayama_generation`), and a module equal to `(x₀,x₁)` times itself is zero
(`MvPolynomial.subsingleton_of_graded_quotient_subsingleton`).

## Implementation details

The proof is the standard minimal-degree argument: the degrees of nonzero homogeneous elements
of a finite graded module are bounded below, and an induction on the degree shows that every
homogeneous element lies in the span of the lifts.
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- Homogeneous lifts of vector-space generators modulo `(x₀,x₁)` generate a finite graded
module. -/
theorem graded_nakayama_generation {k : Type u} [Field k]
    {N : Type v} [AddCommGroup N] [Module (MvPolynomial (Fin 2) k) N]
    [Module k N] [IsScalarTower k (MvPolynomial (Fin 2) k) N]
    [Module.Finite (MvPolynomial (Fin 2) k) N]
    (ℳ : ℤ → AddSubgroup N) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (d : ℕ) (j : ℤ) (f : MvPolynomial (Fin 2) k) (x : N),
      f ∈ homogeneousSubmodule (Fin 2) k d → x ∈ ℳ j → f • x ∈ ℳ ((d : ℤ) + j))
    (r : ℕ) (n : Fin r → N) (hn : ∀ i : Fin r, SetLike.IsHomogeneousElem ℳ (n i))
    (hgen : Submodule.span k (Set.range (fun i : Fin r ↦
      (Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) •
        (⊤ : Submodule (MvPolynomial (Fin 2) k) N)).mkQ (n i))) = ⊤) :
    Submodule.span (MvPolynomial (Fin 2) k) (Set.range n) = ⊤ := by
  classical
  let : DirectSum.Decomposition ℳ := hℳ.chooseDecomposition
  let Q := Submodule.span (MvPolynomial (Fin 2) k) (Set.range n)
  obtain ⟨B, hB⟩ := exists_graded_module_lower_bound ℳ hℳ hsmul
  have hdegrees (a : ℕ) : ∀ (j : ℤ) (x : N), j < B + a → x ∈ ℳ j → x ∈ Q := by
    induction a with
    | zero =>
      intro j x hj hx
      have hzero := hB j x (by simpa using hj) hx
      rw [hzero]
      exact Q.zero_mem
    | succ a ih =>
      intro j x hj hx
      obtain ⟨q, hq, y, hy, z, hz, hxyz⟩ :=
        homogeneous_decomposition_of_quotient_span ℳ hℳ hsmul r n hn hgen j x hx
      rw [hxyz]
      exact Q.add_mem (Q.add_mem hq (Q.smul_mem _ (ih (j - 1) y (by omega) hy)))
        (Q.smul_mem _ (ih (j - 1) z (by omega) hz))
  apply top_unique
  intro x _
  apply DirectSum.Decomposition.inductionOn (ℳ := ℳ)
    (motive := fun x ↦ x ∈ Q) Q.zero_mem ?_ (fun _ _ ↦ Q.add_mem) x
  intro j y
  exact hdegrees ((j - B).toNat + 1) j y (by omega) y.property

/-- A finite graded module with zero quotient modulo `(x₀,x₁)` is zero. -/
theorem subsingleton_of_graded_quotient_subsingleton {k : Type u} [Field k]
    {N : Type v} [AddCommGroup N] [Module (MvPolynomial (Fin 2) k) N]
    [Module.Finite (MvPolynomial (Fin 2) k) N]
    (ℳ : ℤ → AddSubgroup N) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (d : ℕ) (j : ℤ) (f : MvPolynomial (Fin 2) k) (x : N),
      f ∈ homogeneousSubmodule (Fin 2) k d → x ∈ ℳ j → f • x ∈ ℳ ((d : ℤ) + j))
    (hzero : Subsingleton (N ⧸
      (Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) •
        (⊤ : Submodule (MvPolynomial (Fin 2) k) N)))) : Subsingleton N := by
  let : Module k N := Module.compHom N (algebraMap k (MvPolynomial (Fin 2) k))
  let : IsScalarTower k (MvPolynomial (Fin 2) k) N :=
    IsScalarTower.of_compHom k (MvPolynomial (Fin 2) k) N
  have : Subsingleton (N ⧸
      (Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) •
        (⊤ : Submodule (MvPolynomial (Fin 2) k) N))) := hzero
  have hspan := graded_nakayama_generation ℳ hℳ hsmul 0
    (fun i : Fin 0 ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i) (by
      apply Subsingleton.elim)
  have hbot : (⊥ : Submodule (MvPolynomial (Fin 2) k) N) = ⊤ := by
    simpa using hspan
  refine ⟨fun x y ↦ ?_⟩
  have hx : x = 0 := by
    have : x ∈ (⊥ : Submodule (MvPolynomial (Fin 2) k) N) := by
      rw [hbot]
      trivial
    simpa using this
  have hy : y = 0 := by
    have : y ∈ (⊥ : Submodule (MvPolynomial (Fin 2) k) N) := by
      rw [hbot]
      trivial
    simpa using this
  exact hx.trans hy.symm

end MvPolynomial
