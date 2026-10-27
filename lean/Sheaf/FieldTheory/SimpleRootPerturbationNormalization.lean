/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Constructions

/-!
# Integral normalization of coefficient perturbations near a simple root

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, XX 4.4, printed p.374;
the finite valuation estimates in steps 1--3 of simple-root stability.
(blueprint: lem-per-simple-root-perturbation-normalization)
-/

@[expose] public section

universe u v

open Polynomial IsLocalRing
open scoped Topology

namespace AddValuation

/-- Near a simple root, a fixed affine substitution and a fixed nonzero scalar
normalize all sufficiently close coefficient vectors to integral polynomials
whose reduction is `X`. The scaled maximal ideal lies in the prescribed
neighbourhood. This assertion uses no henselianity and asserts no root existence.

Source: ILO, Travaux de Gabber, XX 4.4, printed p.374; the valuation estimates
in steps 1--3 of `lem-per-henselian-simple-root-stability`.
(blueprint: lem-per-simple-root-perturbation-normalization)

Proof:
1. Choose a finite `γ` whose ball about `a` lies in `U`. Put `λ = f'(a)`.
   The constant coefficient of `f(a+Z)` is zero and its linear coefficient is `λ`.
   Write its remaining coefficients as `A_j`. Since the topology is not discrete,
   each ball about zero contains a nonzero element: otherwise translation of
   that ball makes every singleton open. Choose `s ≠ 0` with `v(s)` greater
   than zero, `γ`, and every finite `v(λ)-v(A_j)` for nonzero `A_j`, `j ≥ 2`.
   The finite maximum suffices, without any rank-one or cofinality assumption.
2. For each perturbation write `g(a+Z)-f(a+Z) = ∑ E_j Z^j`. Explicitly
   `E_j = ∑_{j ≤ i < n} (d_i-c_i) binom(i,j) a^(i-j)`, and `E_n=0`.
   For each `j < n` put `t_j = v(λ)+(1-j)v(s)`. Choose a finite bound `η`
   at least every `t_j-v(binom(i,j)*a^(i-j))` with nonzero multiplier.
   If `v(d_i-c_i)>η` for all `i`, the valuation inequality for finite sums
   gives `v(E_j)>t_j`. Zero summands impose no constraint. Each such ball is
   open by the ball basis and the ultrametric inequality; their finite product
   is an open neighbourhood `V` of `c`.
3. Put `t=λ*s` and `H=g(a+sX)/t`. Its constant coefficient is
   `E_0/(λ*s)` of positive value; its linear coefficient is `1+E_1/λ`
   congruent to one; all higher coefficients `(A_j+E_j)*s^(j-1)/λ`
   have positive value. For nonzero `A_j`, the estimate is
   `(v(A_j)+v(s)-v(λ))+(j-2)v(s)>0`; zero coefficients cause no problem.
   Thus every coefficient is in the valuation subring and its reduction is
   `X`. The maximal ideal of the valuation subring consists of the elements
   of positive additive value, since its complement consists exactly of units.
   For `z` in that ideal, `v(s*z)>γ`, hence `a+s*z` lies in `U`.
   The cases `z=0`, zero binomial coefficients, `n=1` and positive
   characteristic all satisfy the same inequalities. -/
theorem exists_open_coefficients_residue_X
    (F : Type u) [Field F] (Γ : Type v) [LinearOrderedAddCommGroupWithTop Γ]
    (v : AddValuation F Γ) [TopologicalSpace F]
    (hvaltop : ∀ x : F, (𝓝 x).HasBasis (fun γ : Γ ↦ γ ≠ ⊤)
      (fun γ ↦ {y : F | γ < v (y - x)}))
    (hnd : ¬ DiscreteTopology F)
    (n : ℕ) (hn : 1 ≤ n) (c : Fin n → F) (a : F)
    (ha : (X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)).IsRoot a)
    (hda : (X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)).derivative.eval a ≠ 0)
    (U : Set F) (hU : IsOpen U) (haU : a ∈ U) :
    ∃ V : Set (Fin n → F), IsOpen V ∧ c ∈ V ∧
      ∃ s t : F, s ≠ 0 ∧ t ≠ 0 ∧
        (∀ z : v.toValuation.valuationSubring,
          z ∈ maximalIdeal v.toValuation.valuationSubring → a + s * (z : F) ∈ U) ∧
        ∀ d : Fin n → F, d ∈ V →
          ∃ H : Polynomial v.toValuation.valuationSubring,
            H.map (residue v.toValuation.valuationSubring) = X ∧
            (X ^ n + ∑ i : Fin n, C (d i) * X ^ (i : ℕ)).comp (C a + C s * X) =
              C t * H.map v.toValuation.valuationSubring.subtype := by sorry

end AddValuation
