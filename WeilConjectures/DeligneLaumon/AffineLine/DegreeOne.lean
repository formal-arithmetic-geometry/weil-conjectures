/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.FourierWeight
public import WeilConjectures.DeligneLaumon.AffineLine.Purity

/-!
# The degree-one estimate for an irreducible factor

Semicontinuity bounds the weights of `j'_*M'` by `v ≤ w + 1` even at the singular points of
the dual line. At the origin the Fourier kernel is trivial, so the stalk formula, taking both
shifts into account, gives

`(FT_ψ(j_*M[1]))_0̄ ≃ RΓ_c(A, j_*M)[2]` and `(j'_*M')_0̄ ≃ H_c^1(A, j_*M)`,

Frobenius-equivariantly. Hence `H_c^1(A, j_*M)` has weights at most `w + 1`. By the
nonexceptionality test `AlgebraicGeometry.isNonexceptional_of_isUnramifiedAtInfinity` the same
bound holds for every irreducible, non-geometrically-constant `M` unramified at infinity.

## Main statements

- `AlgebraicGeometry.hasWeightsAtMost_compactlySupportedCohomology_one`: the degree-one bound
  for an irreducible nonexceptional sheaf pure of weight `w`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable (ψ : AddChar k₀ (PadicAlgCl l))

/-- If `M` is irreducible, nonexceptional for a nontrivial `ψ` and punctually `ι`-pure of
weight `w` on a dense open `U₀` of the affine line, then `H_c^1(A, j_*M)` has weights at most
`w + 1`. (blueprint: `sk-c-dl-a1-hc1`) -/
theorem hasWeightsAtMost_compactlySupportedCohomology_one (ι : PadicAlgCl l →+* ℂ)
    (hψ : ψ ≠ 1) (D : WeilSheaf.LisseOnDenseOpen k₀ l) [Simple D.sheaf]
    (hne : D.sheaf.IsNonexceptional ψ) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    (D.directImage.compactlySupportedCohomology 1).HasWeightsAtMostOver k₀ ι (w + 1) := by
  sorry

end AlgebraicGeometry
