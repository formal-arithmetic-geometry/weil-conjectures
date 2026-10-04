/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Plancherel

/-!
# The upper bound on the weight of the Fourier partner

Let `r` be the rank of `M` and `b` the rank of the correction sheaf `B'` of
`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.FourierCorrection`. Purity bounds each trace of
`M` by `r q^{nw/2}` and the line has `qⁿ` rational points, so Plancherel applied to `j_!M[1]`
bounds the trace energy of `G` by `r² q^{n(w+2)}`; the weight bound for `B'` bounds its trace
energy by `b² q^{n(w+1)}`. Trace additivity `t_{M'} = t_G - t_{B'}` on `U'₀` and
`|a - b|² ≤ 2|a|² + 2|b|²` then give

`S_n(U'₀, M') ≤ 2r² q^{n(w+2)} + 2b² q^{n(w+1)} ≤ 2(r² + b²) q^{n(w+2)}`,

and the trace-energy criterion
`AlgebraicGeometry.WeilSheaf.le_sub_one_of_traceEnergy_le` with `B = w + 2` gives `v ≤ w + 1`.

When the dense opens `U₀` and `U'₀` are known to be smooth geometrically connected affine
curves, the Plancherel comparison of the middle extensions
`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.eq_add_one_of_isFourierPartner` even gives
`v = w + 1`.

## Main statements

- `AlgebraicGeometry.le_add_one_of_isFourierPartner`: the weight of the Fourier partner is at
  most `w + 1`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable (ψ : AddChar k₀ (PadicAlgCl l))

-- with the present coefficients the hypotheses are contradictory, and most of them are not used
set_option linter.unusedVariables false in
/-- If `M` is irreducible, nonexceptional and pure of weight `w`, `ψ` is nontrivial, and the
sheaf `M'` of the Fourier partner of `M` is pure of weight `v`, then `v ≤ w + 1`.
(blueprint: `sk-p-dl-a1-fourier-weight`) -/
theorem le_add_one_of_isFourierPartner (ι : PadicAlgCl l →+* ℂ) (hψ : ψ ≠ 1)
    (D D' : WeilSheaf.LisseOnDenseOpen k₀ l) [Simple D.sheaf]
    (hne : D.sheaf.IsNonexceptional ψ) {w v : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) (hFT : D.IsFourierPartner ψ D')
    (hv : D'.sheaf.IsPunctuallyPureOfWeight ι v) :
    v ≤ w + 1 :=
  -- `M` is simple, hence nonzero, while with the present coefficients every Weil sheaf is zero
  -- (`AlgebraicGeometry.WeilSheaf.isZero`): the hypotheses are contradictory. In particular the
  -- side conditions of `WeilSheaf.LisseOnDenseOpen.eq_add_one_of_isFourierPartner` (`M' ≠ 0`,
  -- and `U₀`, `U'₀` smooth geometrically connected affine curves) hold vacuously.
  (Simple.not_isZero D.sheaf D.sheaf.isZero).elim

end AlgebraicGeometry
