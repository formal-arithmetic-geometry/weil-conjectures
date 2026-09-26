/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension

/-!
# The upper bound on the weight of the Fourier partner

Let `r` be the rank of `M` and `b` the rank of the correction sheaf `B'` of
`WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension`. Purity bounds each trace of `M` by
`r q^{nw/2}` and the line has `qⁿ` rational points, so Plancherel applied to `j_!M[1]` bounds
the trace energy of `G` by `r² q^{n(w+2)}`; the weight bound for `B'` bounds its trace energy
by `b² q^{n(w+1)}`. Trace additivity `t_{M'} = t_G - t_{B'}` on `U'₀` and
`|a - b|² ≤ 2|a|² + 2|b|²` then give

`S_n(U'₀, M') ≤ 2r² q^{n(w+2)} + 2b² q^{n(w+1)} ≤ 2(r² + b²) q^{n(w+2)}`,

and the trace-energy criterion of `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` with
`B = w + 2` gives `v ≤ w + 1`.

## Main statements

- `AlgebraicGeometry.le_add_one_of_isPunctuallyPureOfWeight_of_isFourierPartner`: the weight
  of the Fourier partner is at most `w + 1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] {l : ℕ} [Fact l.Prime]
variable (ψ : AddChar k₀ (PadicAlgCl l)) (k : Type u) [Field k] [Algebra k₀ k] [IsAlgClosed k]

/-- Blueprint `sk-p-dl-a1-fourier-weight`: The Fourier upper weight. If `M` is irreducible,
nonexceptional and pure of weight `w`, and the sheaf `M'` of its Fourier partner is pure of
weight `v`, then `v ≤ w + 1`. -/
theorem le_add_one_of_isPunctuallyPureOfWeight_of_isFourierPartner (ι : PadicAlgCl l →+* ℂ)
    (D D' : LisseOnDenseOpen k₀ l) [Simple D.sheaf] (hne : D.sheaf.IsNonexceptional ψ k)
    {w v : ℝ} (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) (hFT : D.IsFourierPartner ψ D')
    (hv : D'.sheaf.IsPunctuallyPureOfWeight ι v) :
    v ≤ w + 1 := by
  sorry

end AlgebraicGeometry
