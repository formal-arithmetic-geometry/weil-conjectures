/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Order.Field.Rat

/-!
# Rational polyhedral cones have finite rational half-space descriptions

Source: ILO, Travaux de Gabber, Exposé VIII, Remark 3.1.29, printed p. 103
(context on fans only); the constructive proof is supplied by the DAG node.
(blueprint: lem-trf-rational-cone-dual-finite)
-/

@[expose] public section

universe u

namespace Weil

/-- A finitely generated rational cone is the nonnegative locus of finitely many rational forms.
Source: ILO, Travaux de Gabber, Exposé VIII, Remark 3.1.29, printed p. 103, is contextual
only and does not state this theorem. The following proof is the node's agent-written proof.
(blueprint: lem-trf-rational-cone-dual-finite)

1. By `def-weil-finite-dimensional-subspace`, choose a finite spanning list. Remove redundant
   vectors until it is a basis: a nontrivial relation would allow another removal. Its unique
   coordinates are rational linear forms. Both signs of these coordinates cut out the zero cone;
   for the zero vector space this family is empty.
2. Induct on the number of generators. If the old cone is given by `fᵢ ≥ 0`, adjoining a generator
   `v` gives membership precisely when there exists rational `t ≥ 0` with `fᵢ(x) - t fᵢ(v) ≥ 0`
   for every old form, by separating off the last coefficient of the finite sum.
3. Write `aᵢ = fᵢ(v)` and partition the old indices by their zero, positive and negative signs.
   Keep the zero and positive forms and add `gᵢⱼ = aᵢ fⱼ - aⱼ fᵢ` for each positive/negative pair.
   This is a finite family of rational linear forms.
4. A witness `t` satisfies all new inequalities. For positive indices, write
   `fᵢ(x) = (fᵢ(x) - t aᵢ) + t aᵢ`. For pairs the `t` terms cancel, leaving
   `gᵢⱼ(x) = aᵢ (fⱼ(x) - t aⱼ) + (-aⱼ) (fᵢ(x) - t aᵢ) ≥ 0`.
5. Conversely take `T` to be the largest element of the finite set consisting of zero and
   `fⱼ(x) / aⱼ` for negative indices. It is rational and nonnegative. For each positive index,
   the individual inequality gives `0 ≤ fᵢ(x) / aᵢ`, and the mixed inequality gives
   `fⱼ(x) / aⱼ ≤ fᵢ(x) / aᵢ`: their difference is `gᵢⱼ(x) / (aᵢ aⱼ) ≤ 0`.
   Hence `T ≤ fᵢ(x) / aᵢ` for every positive index. For negative indices,
   `T ≥ fⱼ(x) / aⱼ`; multiplying by `aⱼ < 0` reverses the inequality. Together with the zero
   indices, these imply every old inequality at `x - T • v`. Thus `T` is the required witness.
6. Enumerate the final finite family after the induction. Empty sign classes cause no difficulty:
   the lower-bound set always contains zero, and an empty positive class imposes no upper bound.
   An empty old family describes the whole space and stays empty. The base handles `m = 0`,
   and the zero vector space admits an empty family. No pointedness or spanning is assumed.
-/
theorem rationalConeDualFinite {V : Type u} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (m : ℕ) (v : Fin m → V) :
    ∃ s : ℕ, ∃ forms : Fin s → V →ₗ[ℚ] ℚ,
      ∀ x : V,
        (∃ q : Fin m → ℚ, (∀ j : Fin m, 0 ≤ q j) ∧
          (∑ j : Fin m, q j • v j) = x) ↔ ∀ i : Fin s, 0 ≤ forms i x := by
  sorry

end Weil
