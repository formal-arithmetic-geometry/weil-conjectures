/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Finiteness
public import WeilConjectures.ZetaFunction.Examples
public import WeilConjectures.ZetaFunction.TraceFormula

/-!

# Frobenius on the projective line

For `X₀ = ℙ¹` over `k₀ = 𝔽_q`, constant coefficients `ℚ̄_ℓ` and `m ≥ 1`, both sides of the trace
formula for the `m`-th power of Frobenius are `1 + qᵐ` (blueprint
`example-frobenius-projective-line`): `Φ_m` has the `qᵐ + 1` fixed points of `ℙ¹(𝔽_{qᵐ})`,
geometric Frobenius `F` acts on `H⁰(ℙ¹ ⊗ k̄, ℚ̄_ℓ)` by `1`, and `∑ᵢ (-1)ⁱ Tr(Fᵐ | Hⁱ) = 1 + qᵐ`.

## Main statements

- `AlgebraicGeometry.projectiveLine_frobenius_trace_formula`: blueprint
  `example-frobenius-projective-line`.

## Implementation notes

The local side is stated as the point count `#ℙ¹(𝔽_{qᵐ})`, the number of fixed points of `Φ_m`,
each of local term `1` for the constant sheaf; the global side is the alternating trace of `Fᵐ`
on the cohomology `Hⁱ(ℙ¹ ⊗ k̄, ℚ̄_ℓ)` of the Weil sheaf `ℚ̄_ℓ`. The degree-wise values
`H¹ = 0` and `Tr(Fᵐ | H²) = qᵐ` are not included: in the library they rest on Poincaré duality
(`AlgebraicGeometry.WeilSheaf.poincareDuality`), which still depends on `sorry`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (k : Type u) [Field k] [Finite k] (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)]

/-- Blueprint `example-frobenius-projective-line`: let `X₀ = ℙ¹` over `k = 𝔽_q` and `m ≥ 1`.

* (local side) the fixed points of the `m`-th power of Frobenius are the points of
  `ℙ¹(𝔽_{qᵐ})`, and there are `qᵐ + 1` of them;
* (global side) `Fᵐ` acts on `H⁰(ℙ¹ ⊗ k̄, ℚ̄_ℓ)` with trace `1`, and
  `∑ᵢ (-1)ⁱ Tr(Fᵐ | Hⁱ(ℙ¹ ⊗ k̄, ℚ̄_ℓ)) = 1 + qᵐ`, so that
  `Tr(Fᵐ | H²) - Tr(Fᵐ | H¹) = qᵐ`.

The finer statements `H¹ = 0` and `F = q` on the line `H²` are not proved here: in the library
they rest on Poincaré duality (`AlgebraicGeometry.WeilSheaf.poincareDuality`), which is not yet
free of `sorry`. -/
theorem projectiveLine_frobenius_trace_formula {m : ℕ} (hm : 1 ≤ m) :
    (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).pointCount m = Nat.card k ^ m + 1 ∧
    LinearMap.trace (PadicAlgCl l) _
        (((WeilSheaf.adicConstant k l (ProjectiveLine (Spec (.of k)))).cohomology
          ((0 : ℕ) : ℤ)).frobeniusEnd ^ m) = 1 ∧
    ∑ i ∈ Finset.range 3, (-1) ^ i * LinearMap.trace (PadicAlgCl l) _
        (((WeilSheaf.adicConstant k l (ProjectiveLine (Spec (.of k)))).cohomology
          (i : ℤ)).frobeniusEnd ^ m) = 1 + (Nat.card k : PadicAlgCl l) ^ m ∧
    LinearMap.trace (PadicAlgCl l) _
        (((WeilSheaf.adicConstant k l (ProjectiveLine (Spec (.of k)))).cohomology
          ((2 : ℕ) : ℤ)).frobeniusEnd ^ m) -
      LinearMap.trace (PadicAlgCl l) _
        (((WeilSheaf.adicConstant k l (ProjectiveLine (Spec (.of k)))).cohomology
          ((1 : ℕ) : ℤ)).frobeniusEnd ^ m) = (Nat.card k : PadicAlgCl l) ^ m := by
  set Y := ProjectiveLine (Spec (.of k))
  have hN := pointCount_projectiveLine k (n := m) (by omega)
  have hsum := WeilSheaf.pointCount_eq_sum_trace_cohomology k l Y 1 hm
  have h0 : LinearMap.trace (PadicAlgCl l) _
      (((WeilSheaf.adicConstant k l Y).cohomology ((0 : ℕ) : ℤ)).frobeniusEnd ^ m) = 1 := by
    have h : ((WeilSheaf.adicConstant k l Y).cohomology 0).frobeniusEnd = 1 := by
      rw [FrobeniusModule.frobeniusEnd, WeilSheaf.frobenius_cohomology_zero_adicConstant]
      rfl
    rw [Nat.cast_zero, h, one_pow, LinearMap.trace_one,
      WeilSheaf.finrank_cohomology_zero_adicConstant, Nat.cast_one]
  rw [hN] at hsum
  push_cast at hsum
  refine ⟨hN.trans (add_comm _ _), h0, hsum.symm, ?_⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, h0] at hsum
  linear_combination -hsum

end AlgebraicGeometry
