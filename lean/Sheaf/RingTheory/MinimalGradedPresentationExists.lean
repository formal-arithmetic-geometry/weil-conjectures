/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Sheaf.RingTheory.GradedNakayamaGeneration

/-!
# Existence of minimal finite graded free presentations

Source: blueprint `lem-sc-p1-graded-resolution`, graded Nakayama construction of a minimal
presentation, expanded from the DAG (blueprint: lem-sc-p1-minimal-graded-presentation-exists).
-/

@[expose] public section

universe u

namespace MvPolynomial

/-- Every finite homogeneous spanning set admits a minimal finite graded free presentation.
Source: step 1 of DAG node `lem-sc-p1-graded-nakayama-free`, refining the graded Hilbert
syzygy argument cited in blueprint `lem-sc-p1-graded-resolution`. The construction below is the
standard agent-written expansion of that step, rather than a quoted blueprint proof.
(blueprint: lem-sc-p1-minimal-graded-presentation-exists)

Proof: restrict scalars along the constant-polynomial embedding to give `N` its `k`-module
structure. Put `I = (x₀,x₁)` and `Q = N/IN`. In `Q`, multiplication by a polynomial equals
multiplication by its constant coefficient: the difference lies in `I` and acts by zero. Hence
the images of the given finite homogeneous generating set span `Q` over `k`. Extract a basis
from this finite spanning family and retain its original homogeneous lifts `nᵢ`, with degrees
`dᵢ`. Set `F = Fin r → S`. Its degree-`j` subgroup consists of coefficient tuples whose ith
coordinate is homogeneous of degree `j-dᵢ` (zero if that degree is negative). Decompose every
polynomial coordinate into its homogeneous components, translate their degrees by `dᵢ`, and sum
over the finite union of these translated supports. Uniqueness of polynomial homogeneous
components gives uniqueness of this decomposition; homogeneous multiplication adds degrees.
The standard basis vector `eᵢ` has degree `dᵢ`. Define `q(a) = ∑ i, aᵢ • nᵢ`. Scalar
compatibility in `N` shows it preserves degrees. Graded Nakayama generation, applied to the
chosen lifts, makes `q` surjective. If `q(a)` belongs to `IN`, linear independence of the chosen
basis of `Q` forces every constant coefficient of `aᵢ` to vanish. Each `aᵢ` then lies in `I`,
so the finite basis expansion shows `a` belongs to `IF`. This proves minimality. For `Q = 0`,
the chosen basis is empty; graded Nakayama gives `N = 0`, yielding the zero presentation. -/
theorem exists_minimal_graded_presentation (k : Type u) [Field k]
    (N : Type u) [AddCommGroup N] [Module (MvPolynomial (Fin 2) k) N]
    (ℳ : ℤ → AddSubgroup N) (hℳ : DirectSum.IsInternal ℳ)
    (hsmul : ∀ (n : ℕ) (j : ℤ) (f : MvPolynomial (Fin 2) k) (x : N),
      f ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℳ j →
        f • x ∈ ℳ ((n : ℤ) + j))
    (hN : ∃ s : Set N, s.Finite ∧
      (∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x) ∧
      Submodule.span (MvPolynomial (Fin 2) k) s = ⊤) :
    ∃ (F : ModuleCat.{u} (MvPolynomial (Fin 2) k)) (ℱ : ℤ → AddSubgroup F),
      DirectSum.IsInternal ℱ ∧
      (∀ (n : ℕ) (j : ℤ) (f : MvPolynomial (Fin 2) k) (x : F),
        f ∈ homogeneousSubmodule (Fin 2) k n → x ∈ ℱ j →
          f • x ∈ ℱ ((n : ℤ) + j)) ∧
      ∃ (r : ℕ) (b : Module.Basis (Fin r) (MvPolynomial (Fin 2) k) F)
        (d : Fin r → ℤ),
        (∀ i : Fin r, b i ∈ ℱ (d i)) ∧
        ∃ q : F →ₗ[MvPolynomial (Fin 2) k] N,
          Function.Surjective q ∧
          (∀ (j : ℤ) (x : F), x ∈ ℱ j → q x ∈ ℳ j) ∧
          (∀ x : F,
            q x ∈ Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) •
              (⊤ : Submodule (MvPolynomial (Fin 2) k) N) →
            x ∈ Ideal.span (Set.range (X : Fin 2 → MvPolynomial (Fin 2) k)) •
              (⊤ : Submodule (MvPolynomial (Fin 2) k) F)) := by
  sorry

end MvPolynomial
