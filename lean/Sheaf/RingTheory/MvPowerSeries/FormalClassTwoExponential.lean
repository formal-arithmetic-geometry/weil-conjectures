/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.RingTheory.MvPowerSeries.BivariateExp
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.List.OfFn

/-!
# Formal exponential factorization with central pairwise brackets

Source: agent-stated formal coefficient identity, motivated by Milne, Algebraic Groups,
§23h, equation (153), printed p.510. Milne does not state this identity; the node supplies
its coefficient proof (blueprint: lem-sfb-formal-class-two-exponential).
-/

@[expose] public section

universe u

namespace MvPowerSeries

/-- Formal exponential factorization for a finite ordered family with vanishing triple
commutators. The bracket is Mathlib's associative commutator `X * Y - Y * X`, as in
[def-wf-lie-algebra]. The `List.ofFn` product is in increasing `Fin r` order.

Source: agent-stated class-two identity; Milne, Algebraic Groups, §23h, equation (153),
printed p.510, motivation only. Bourbaki, Lie Groups and Lie Algebras, Chapter II,
Campbell--Hausdorff specialization remains WANTED
(blueprint: lem-sfb-formal-class-two-exponential).

Proof:
1. Write `X_i = Z_i`, `S = ∑ i, X_i`, `C_ij = [X_i,X_j]` and `C = ∑ i<j, C_ij`.
The hypothesis says `C_ij X_k = X_k C_ij`. By induction and rational linearity,
`C` commutes with every power of each `X_k`. This uses the associative example of
[def-wf-lie-algebra], not centrality in the entire series algebra.
2. In the auxiliary central variable `u`, put `E_i = ∑ n, u^n X_i^n/n!`,
`E_S = ∑ n, u^n S^n/n!` and `Q = ∑ n, u^(2*n) (-C/2)^n/n!`.
The coefficient derivative satisfies Leibniz: at degree `n`, the terms indexed by
`p+q=n+1` have weights `p` and `q`, adding to `n+1`, without changing factor order.
3. Direct coefficient calculation gives `D E_i = X_i E_i`, `D E_S = S E_S` and
`D Q = -u C Q`. The last formula at degree `2*n-1` is the factorial identity
`2*n*(-C/2)^n/n! = -C*(-C/2)^(n-1)/(n-1)!`; the even coefficients vanish.
All these series have constant coefficient one, and `C` commutes with every `E_i`.
4. Induction gives `X_i^n X_j = X_j X_i^n + n C_ij X_i^(n-1)` for `n ≥ 1`:
multiply on the left by `X_i` and use `X_i X_j = X_j X_i + C_ij` and
`X_i C_ij = C_ij X_i`. Dividing coefficientwise by `n!` yields
`E_i X_j = (X_j + u C_ij) E_i`, including the constant coefficient.
5. Descending induction through the prefix `P_j = E_1 ... E_(j-1)` yields
`P_j X_j = (X_j + u ∑ i<j, C_ij) P_j`. Each step uses step 4 and commutes the
correction past earlier factors using step 1; the empty prefix is the base case.
6. The finite product rule gives `D F = (S+u C) F` for `F = E_1 ... E_r`:
the term differentiating `E_j` is transformed by step 5, then summed over `j`.
This includes `r=0`, since `D 1=0`. Also `F C = C F`.
7. Thus `H = F Q` satisfies `D H = S H` and `H(0)=1`. Its coefficients obey
`(n+1) h_(n+1) = S h_n`. Division by the nonzero rational `n+1` and induction
give `h_n = S^n/n!`, hence `E_S = F Q`. No domain assumption is used.
8. A product of `n` zero-constant series has no coefficient below total degree `n`.
Thus, at each `s^a t^b`, the coefficients in the auxiliary variable are polynomials
of degree at most `a+b`; for `C^n` the lower degree bound is `2*n`.
The same bound holds for finite products by the Cauchy formula. Evaluate these finite
polynomials at `u=1` to obtain precisely the `bivariateExp` coefficients on both sides.
Coefficient extensionality proves the identity. The empty family gives `exp(0)=1`,
and for one input the correction is also one. -/
theorem bivariateExp_sum_eq_orderedProd_mul_correction
    {A : Type u} [Ring A] [Algebra ℚ A] (r : ℕ)
    (Z : Fin r → MvPowerSeries (Fin 2) A)
    (hZ : ∀ i : Fin r, constantCoeff (Z i) = 0)
    (hcentral : ∀ i j k : Fin r, ⁅⁅Z i, Z j⁆, Z k⁆ = 0) :
    bivariateExp (∑ i : Fin r, Z i) =
      (List.ofFn (fun i : Fin r => bivariateExp (Z i))).prod *
        bivariateExp ((-(1 / 2 : ℚ)) •
          (∑ i : Fin r, ∑ j ∈ Finset.univ.filter (fun j : Fin r => i < j), ⁅Z i, Z j⁆)) := by
  sorry

end MvPowerSeries
