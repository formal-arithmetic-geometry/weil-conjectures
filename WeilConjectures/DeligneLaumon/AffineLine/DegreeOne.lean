/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension

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

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable (ψ : AddChar k₀ (PadicAlgCl l)) (k : Type u) [Field k] [Algebra k₀ k] [IsAlgClosed k]

/-- Blueprint `sk-c-dl-a1-hc1`: The degree-one estimate for an irreducible factor. If `M` is
irreducible, nonexceptional and punctually `ι`-pure of weight `w` on a dense open `U₀` of the
affine line, then `H_c^1(A, j_*M)` has weights at most `w + 1`. -/
theorem hasWeightsAtMost_compactlySupportedCohomology_one (ι : PadicAlgCl l →+* ℂ)
    (D : LisseOnDenseOpen k₀ l) [Simple D.sheaf] (hne : D.sheaf.IsNonexceptional ψ k)
    {w : ℝ} (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    (D.directImage.compactlySupportedCohomology 1).HasWeightsAtMost ι (Nat.card k₀)
      (w + 1) := by
  sorry

end AlgebraicGeometry
