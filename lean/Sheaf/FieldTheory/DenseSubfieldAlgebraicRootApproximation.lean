/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Field.Approximation

/-! # Algebraic root approximation over a dense subfield

Source: Stanford Weil II seminar, L19, Proposition 1.1.9, first bullet, p. 3,
countability input; quantitative subargument of
`WeilConjectures/NumberTheory/Padics/Extension.lean`, lines 110–126, using
`Mathlib/Analysis/Normed/Field/Approximation.lean`, lines 114–138
(blueprint: lem-sfb-dense-subfield-algebraic-root-approximation).

The field `D` has no norm. Its map into `L` is explicitly the composite through `K`.
The expressions for the tolerance and the root bound are expanded to avoid local lets.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Polynomial

/-- A root of a monic polynomial over `K` can be approximated within any positive
radius by a root algebraic over a dense subfield `D`, with the specified coefficient tolerance.

Source: Stanford Weil II seminar, L19, Proposition 1.1.9, first bullet, p. 3,
countability input; quantitative subargument of the project's p-adic Extension module,
lines 110–126, using Mathlib's normed-field polynomial approximation theorems
(blueprint: lem-sfb-dense-subfield-algebraic-root-approximation).

Proof:
1. Set M = max(norm x, 1), t = r / M and epsilon = t^n / (n + 1). Since M >= 1,
   r > 0 and n >= 1, epsilon is positive, and taking the positive real nth root gives
   ((n + 1) * epsilon)^(1/n) * M = r.
2. Apply lem-sfb-monic-dense-approximation to D -> K and epsilon. It gives a monic
   polynomial g of degree n whose coefficientwise image h differs from f by less than
   epsilon in every coefficient. No norm on D is needed.
3. By def-weil-polynomial-ring the field inclusions preserve the leading coefficient 1
   and every zero coefficient above degree n. Thus h and its image in L are monic of
   degree n. Apply lem-weil-alg-closed-linear-factorization to the image of h in L.
   Its leading coefficient is 1, and comparison of degrees gives n linear factors.
4. Apply lem-sfb-roots-coefficient-proximity to f, h, x and epsilon, using equal positive
   degrees, monicity, the coefficient inequalities, splitting and the extending norm.
   It gives a root b of h with the displayed bound; step 1 identifies that bound with r.
5. By def-weil-polynomial-root, evaluation of h at b uses the same composite coefficient
   map D -> K -> L as evaluation of g. Hence both evaluations vanish. Monicity makes g
   nonzero, so def-weil-algebraic-element implies that b is algebraic over D.
-/
theorem exists_algebraic_root_approximation_of_denseRange
    (D : Type u) (K : Type v) (L : Type w) [Field D] [NormedField K] [NormedField L]
    [Algebra D K] [NormedAlgebra K L] [IsAlgClosed L]
    (hd : DenseRange (algebraMap D K)) (f : Polynomial K) (hf : f.Monic)
    (n : ℕ) (hn : 1 ≤ n) (hdegree : f.natDegree = n)
    (x : L) (hx : f.eval₂ (algebraMap K L) x = 0) (r : ℝ) (hr : 0 < r) :
    ∃ (g : Polynomial D) (b : L),
      g.Monic ∧ g.natDegree = n ∧
      (g.map (algebraMap D K)).Monic ∧ (g.map (algebraMap D K)).natDegree = n ∧
      ((g.map (algebraMap D K)).map (algebraMap K L)).Splits ∧
      (∀ i : ℕ, ‖(g.map (algebraMap D K)).coeff i - f.coeff i‖ <
        (r / max ‖x‖ 1) ^ n / (n + 1 : ℝ)) ∧
      (g.map (algebraMap D K)).eval₂ (algebraMap K L) b = 0 ∧
      g.eval₂ ((algebraMap K L).comp (algebraMap D K)) b = 0 ∧
      ‖x - b‖ <
        ((n + 1 : ℝ) * ((r / max ‖x‖ 1) ^ n / (n + 1 : ℝ))) ^ (n : ℝ)⁻¹ * max ‖x‖ 1 ∧
      ((n + 1 : ℝ) * ((r / max ‖x‖ 1) ^ n / (n + 1 : ℝ))) ^ (n : ℝ)⁻¹ * max ‖x‖ 1 = r ∧
      @IsAlgebraic D L _ _
        ((algebraMap K L).comp (algebraMap D K)).toAlgebra b := by
  sorry

end Polynomial
