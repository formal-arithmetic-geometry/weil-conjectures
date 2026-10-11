/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finite subalgebras with prescribed fraction field

Source: Stacks Project, More on Algebra, Tag 07PR, proof, finite algebra model paragraph
(blueprint: lem-weil-pbc-finite-subalgebra-fraction-field).
-/

universe u v w

namespace MvPolynomial

/-- For `A = k[[x₁, …, xₙ]][y₁, …, yₘ]` in positive characteristic, `A` is a domain and
any finite extension `M` of its fraction field has a finite `A`-subalgebra with fraction
field `M`. The scalar tower identifies the structural map `A → M` with `A → K → M`.
Source: Stacks Project, More on Algebra, Tag 07PR, proof, finite algebra model paragraph
(blueprint: lem-weil-pbc-finite-subalgebra-fraction-field).

Proof (the source asserts the model's existence; the DAG supplies denominator clearing):
1. Power series over a field have no zero divisors, and polynomials over a domain form a
   domain (lem-weil-pbc-power-series-domain, lem-weil-pbc-polynomial-ring-domain).
   Localization at the zero prime therefore gives the fraction field `K`, with injective
   maps `A → K → M` (def-weil-pbc-localization-at-prime, def-pc-field-extension).
2. Choose a finite `K`-spanning set `e₁, …, eᵣ` of `M`
   (def-weil-finitely-generated-module). Each generator satisfies a monic equation over
   `K` (lem-weil-pbc-finite-algebra-is-integral).
3. Write all coefficients as fractions over `A`. Their nonzero denominators have a
   nonzero product `δ`. For an equation of degree `d` with coefficients `cⱼ`, multiplying
   by `δ^d` gives a monic equation for `fᵢ = δ eᵢ`, with coefficients `δ^j cⱼ` in `A`.
4. Let `B = A[f₁, …, fᵣ]`. It is a subring containing `A`. Since its finitely many
   algebra generators are integral, it is finite as an `A`-module
   (lem-weil-pbc-finite-of-integral-generators, def-weil-polynomial-ring).
5. Express `z ∈ M` as `∑ kᵢ eᵢ`, and write `kᵢ = aᵢ/tᵢ` with nonzero `tᵢ ∈ A`.
   Then `s = δ ∏ tᵢ` is nonzero and belongs to `A ⊆ B`, while
   `s z = ∑ aᵢ (∏_{l ≠ i} tₗ) fᵢ` belongs to `B`. Thus `z = b/s` as claimed. -/
theorem exists_finite_subalgebra_fraction_field
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (n m : ℕ)
    (K : Type v) [Field K]
    [Algebra (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K]
    [IsLocalization.AtPrime K
      (⊥ : Ideal (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))]
    (M : Type w) [Field M] [Algebra K M]
    [Algebra (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) M]
    [IsScalarTower (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) K M]
    [Module.Finite K M] :
    IsDomain (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) ∧
      ∃ B : Subalgebra (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) M,
        Module.Finite (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)) B ∧
          ∀ z : M, ∃ b s : B, (s : M) ≠ 0 ∧ z = (b : M) / (s : M) := by
  sorry

end MvPolynomial
