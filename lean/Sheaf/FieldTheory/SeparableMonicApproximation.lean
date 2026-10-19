/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.FieldTheory.Separable
import Sheaf.FieldTheory.PolynomialConstantShiftsFiniteExceptions

/-!
# Approximation by monic separable polynomials

Source: the auxiliary separable approximation for Temkin, Stable Modification,
Theorem 3.5.5, Step 3, printed p. 22; agent-supplied argument using the separability
convention of Stacks Project, Tag 09H1 (blueprint: lem-trf-separable-monic-approximation).
-/

@[expose] public section

universe u

namespace Polynomial

/-- Over a field with a nontrivial real-valued nonarchimedean absolute value, every monic
polynomial of positive degree admits arbitrarily close monic separable approximations
of the same degree, coefficient by coefficient below the leading term.

Source: auxiliary approximation for Temkin, Stable Modification, Theorem 3.5.5, Step 3,
printed p. 22; the argument is agent-supplied, with separability as in Stacks Tag 09H1
(blueprint: lem-trf-separable-monic-approximation).

Proof plan: If `d = 1`, take `g = f`, whose derivative is one. Otherwise `d >= 2`.
Nontriviality gives a nonzero `t` with `0 < v t < 1`, replacing an element by its inverse
if necessary. The powers of `t` are distinct and tend to zero: for `r = v t` and
`c = r⁻¹ - 1 > 0`, Bernoulli's inequality gives `r^n <= (1 + n*c)⁻¹`.
Thus arbitrarily small nonzero powers avoid any specified finite subset of the field.
There is at most one `a` such that `derivative f + C a = 0`; choose a power outside
this set with `v a < ε`. Then `h = f + C a * X` is monic of degree `d` and has nonzero
derivative. By lem-trf-polynomial-constant-shifts-finite-exceptions, only finitely many
`b` make `h + C b` inseparable. Choose another power outside that finite set with
`v b < ε`, and put `g = f + C a * X + C b`. Both perturbations have degree below `d`.
The coefficient differences at indices zero and one are `b` and `a`, respectively,
and those at all higher indices below `d` are zero. These give all the required bounds.
No completeness or perfectness is used. -/
theorem exists_monic_separable_natDegree_eq_coeff_sub_lt
    {F : Type u} [Field F] (v : AbsoluteValue F ℝ) (hv : v.IsNontrivial)
    (hna : ∀ x y : F, v (x + y) ≤ max (v x) (v y))
    (f : F[X]) (hf : f.Monic) (d : ℕ) (hd : 1 ≤ d) (hfd : f.natDegree = d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : F[X], g.Monic ∧ g.Separable ∧ g.natDegree = d ∧
      ∀ i : ℕ, i < d → v (g.coeff i - f.coeff i) < ε := by
  sorry

end Polynomial
