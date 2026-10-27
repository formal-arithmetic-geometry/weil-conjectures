/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Separable
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-! # Norm extension and minimal-polynomial root separation over the p-adic numbers

Source: Stanford Weil II seminar, L19, Proposition 1.1.9, first bullet, p. 3,
countability input; the agent-supplied argument in
`WeilConjectures/NumberTheory/Padics/Extension.lean`, lines 84–109
(blueprint: lem-sfb-padic-minpoly-normed-separation).

The extended norm is bundled as a real-valued absolute value. The other-root set and
its separation radius are specified by equalities, including the empty-set branch.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Padic

/-- Any algebraic closure of the p-adic field has an extending nonarchimedean norm,
and each minimal polynomial has distinct roots with the stated positive separation radius.

Source: Stanford Weil II seminar, L19, Proposition 1.1.9, first bullet, p. 3,
countability input; agent-supplied subargument of
`WeilConjectures/NumberTheory/Padics/Extension.lean`, lines 84–109
(blueprint: lem-sfb-padic-minpoly-normed-separation).

Proof:
1. By def-weil-l-adic-numbers, the base is complete, nonarchimedean, and of
   characteristic zero. Its norm is nontrivial since the norm of the prime is its
   reciprocal, strictly between zero and one. Rational Cauchy sequences representing
   p-adic numbers give rational approximation within any positive real radius.
2. Algebraicity follows from def-weil-algebraic-closure. Apply
   lem-trf-spectral-norm-algebraic-extension to the complete, nontrivially normed,
   nonarchimedean base and this algebraic extension. Its spectral norm gives the
   absolute value, all its norm laws, and the metric with distance v(z - w).
3. For x, def-weil-pbc-separable-algebraic-extension gives its monic irreducible
   minimal polynomial f and f(x) = 0. Its degree is positive: otherwise it is the
   monic constant 1, which cannot vanish (def-weil-polynomial-ring and
   def-weil-polynomial-root).
4. The coefficient of degree n - 1 in the derivative of the monic degree-n
   polynomial f is n, nonzero in characteristic zero. Thus the derivative is not
   zero. Apply lem-trf-irreducible-separable-derivative, then
   lem-pc-separable-polynomial-distinct-roots-alg-closed, to obtain n distinct
   roots and the product of their linear factors.
5. The set S of other roots is finite. Each v(x - y) for y in S is positive by
   definiteness. If S is empty, delta = 1 is positive and the bound is vacuous.
   Otherwise its finite nonempty distance image has a least member: induct on the
   finite set, adjoining each new member by a binary minimum. This member is its
   real infimum, is positive, and bounds every other-root distance from below.
-/
theorem exists_absoluteValue_minpoly_separation_of_isAlgClosure
    (ell : ℕ) [Fact ell.Prime] (Ω : Type u) [Field Ω]
    [Algebra (Padic ell) Ω] [IsAlgClosure (Padic ell) Ω] :
    CompleteSpace (Padic ell) ∧ CharZero (Padic ell) ∧
      IsUltrametricDist (Padic ell) ∧
      (∃ z : Padic ell, 1 < ‖z‖) ∧
      (∀ (z : Padic ell) (r : ℝ), 0 < r → ∃ q : ℚ, ‖z - q‖ < r) ∧
      ∃ v : AbsoluteValue Ω ℝ,
        (∀ z : Padic ell, v (algebraMap (Padic ell) Ω z) = ‖z‖) ∧
        IsNonarchimedean (v : Ω → ℝ) ∧
        (∃ m : MetricSpace Ω, ∀ z w : Ω, @dist Ω m.toDist z w = v (z - w)) ∧
        ∀ x : Ω, ∃ f : Polynomial (Padic ell),
          f = minpoly (Padic ell) x ∧ f.Monic ∧ Irreducible f ∧ f.Separable ∧
          1 ≤ f.natDegree ∧ f.aeval x = 0 ∧
          (∃ roots : Fin f.natDegree → Ω,
            Function.Injective roots ∧ (∀ i : Fin f.natDegree, f.aeval (roots i) = 0) ∧
            f.map (algebraMap (Padic ell) Ω) =
              ∏ i : Fin f.natDegree, (Polynomial.X - Polynomial.C (roots i))) ∧
          ∃ S : Set Ω, S = {y : Ω | f.aeval y = 0 ∧ y ≠ x} ∧ S.Finite ∧
            ∃ δ : ℝ,
              δ = (if S = ∅ then 1 else sInf ((fun y : Ω ↦ v (x - y)) '' S)) ∧
              0 < δ ∧ ∀ y ∈ S, δ ≤ v (x - y) := by
  sorry

end Padic
