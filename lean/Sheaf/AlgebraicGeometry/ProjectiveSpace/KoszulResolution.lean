/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# The graded Koszul resolution on two polynomial variables

Source: literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-duality/
lem-sc-p1-graded-resolution.md, graded-resolution source note
(blueprint: lem-sc-p1-koszul-resolution).

`S = MvPolynomial (Fin 2) k` is graded by total degree through Mathlib's
`homogeneousSubmodule`, extended by zero in negative degrees, as in the landed
`MvPolynomial.exists_graded_free_resolution_two` (lem-sc-p1-graded-syzygy).
The underlying modules of `S(-2)` and `S(-1)` are `S`; by
`def-weil-pbc-proj-twisting-sheaf` (2), `S(d)_n = S_{d+n}`, so the degree `n + 2`
part of `S(-2)` is `S_n` and the degree `n + 1` part of `S(-1)` is `S_n`; all lower
parts are zero. The quotient `k = S/(x₀,x₁)` has the quotient grading, concentrated
in degree zero.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.ProjectiveLine

open MvPolynomial

/-- The exact graded Koszul resolution `0 → S(-2) → S(-1)² → S → S/(x₀,x₁) → 0`.
Source: the blueprint `lem-sc-p1-graded-resolution`, graded-resolution source note;
Stacks Algebra, Section 00JL, for the shift convention
(blueprint: lem-sc-p1-koszul-resolution).

The maps are `a ↦ (a x₁, -a x₀)`, `(a, b) ↦ a x₀ + b x₁` and the quotient map.
Degree zero: since negative-degree parts vanish, `f` sends `S(-2)_{n+2} = S_n` into
`S(-1)²_{n+2} = S_{n+1}²`, `g` sends `S(-1)²_{n+1} = S_n²` into `S_{n+1}`, and `q`
kills `S_{n+1}` (the quotient is concentrated in degree zero), for every `n : ℕ`.

Proof, following the node's four steps:
1. The shifts `M(d)_n = M_{d+n}` of `def-weil-pbc-proj-twisting-sheaf` make
   the two multiplication maps degree preserving. Commutativity gives their zero
   composite. The quotient kernel is `(x₀,x₁)`, the image of the second map.
2. `lem-weil-pbc-polynomial-ring-domain` says `S` is a domain. Since `x₀` is
   nonzero, `a*x₀ = 0` implies `a = 0`, giving injectivity of the first map.
3. `lem-sc-p1-linear-syzygy` gives `a = c*x₁` and `b = -c*x₀` whenever
   `a*x₀ + b*x₁ = 0`. Thus the middle kernel is the first image; the converse
   follows from step 1.
4. Assemble these kernel-image equalities and the surjective quotient map.
   Positive-degree monomials lie in `(x₀,x₁)`, so the quotient map is homogeneous
   into the quotient concentrated in degree zero. -/
theorem koszul_resolution {k : Type u} [Field k] :
    ∃ (f : MvPolynomial (Fin 2) k →ₗ[MvPolynomial (Fin 2) k]
          MvPolynomial (Fin 2) k × MvPolynomial (Fin 2) k)
      (g : MvPolynomial (Fin 2) k × MvPolynomial (Fin 2) k →ₗ[MvPolynomial (Fin 2) k]
          MvPolynomial (Fin 2) k)
      (q : MvPolynomial (Fin 2) k →ₗ[MvPolynomial (Fin 2) k]
          MvPolynomial (Fin 2) k ⧸
            Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 2) k))),
      (∀ a : MvPolynomial (Fin 2) k, f a = (a * X 1, -a * X 0)) ∧
      (∀ p : MvPolynomial (Fin 2) k × MvPolynomial (Fin 2) k,
        g p = p.1 * X 0 + p.2 * X 1) ∧
      (∀ a : MvPolynomial (Fin 2) k,
        q a = Ideal.Quotient.mk (Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 2) k))) a) ∧
      Function.Injective f ∧ Function.Exact f g ∧
      Function.Exact g q ∧ Function.Surjective q ∧
      (∀ a : MvPolynomial (Fin 2) k,
        q a = 0 ↔ a ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 2) k))) ∧
      (∀ a : MvPolynomial (Fin 2) k, g (f a) = 0) ∧
      (∀ (n : ℕ) (a : MvPolynomial (Fin 2) k), a ∈ homogeneousSubmodule (Fin 2) k n →
        (f a).1 ∈ homogeneousSubmodule (Fin 2) k (n + 1) ∧
        (f a).2 ∈ homogeneousSubmodule (Fin 2) k (n + 1)) ∧
      (∀ (n : ℕ) (p : MvPolynomial (Fin 2) k × MvPolynomial (Fin 2) k),
        p.1 ∈ homogeneousSubmodule (Fin 2) k n → p.2 ∈ homogeneousSubmodule (Fin 2) k n →
        g p ∈ homogeneousSubmodule (Fin 2) k (n + 1)) ∧
      (∀ (n : ℕ) (a : MvPolynomial (Fin 2) k),
        a ∈ homogeneousSubmodule (Fin 2) k (n + 1) → q a = 0) := by
  sorry

end AlgebraicGeometry.ProjectiveLine
