/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension

/-!
# The generic Fourier sheaf is pure of some weight

Write `M^c = M^∨ ⊗ T_w` for the conjugate of a sheaf pure of weight `w`, where `T_w` is the
constant Weil line whose Frobenius has realization `q^w`. On a common dense lisse open the
paired complex `FT_ψ(j_!M[1]) ⊕ FT_{ψ⁻¹}(j_!M^c[1])` is `H[1]` for a lisse sheaf `H`, and the
Fourier trace identity makes every point trace of `H` a sum `-∑_x (a_x ψ_n(xy) + a̅_x ψ_n(xy)⁻¹)`,
which is real. Newton's identities then make every local characteristic polynomial real, so
`H` is `ι`-real; real-sheaf purity gives each of its irreducible constituents, in particular
`M'`, a real weight, and semicontinuity extends purity to the whole lisse domain of `M'`.

Forming the conjugate envelope *after* extending by zero is what avoids assuming reality of
`j_*M` itself.

## Main statements

- `AlgebraicGeometry.exists_isPunctuallyPureOfWeight_of_isFourierPartner`: the Fourier
  partner of an irreducible nonexceptional pure sheaf is pure of some real weight.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable (ψ : AddChar k₀ (PadicAlgCl l))

/-- For an irreducible nonexceptional `M` pure of weight `w` and a nontrivial `ψ`, the
irreducible lisse sheaf `M'` of its Fourier partner is punctually `ι`-pure of some real weight
`v`. (blueprint: `sk-p-dl-a1-some-weight`) -/
theorem exists_isPunctuallyPureOfWeight_of_isFourierPartner (ι : PadicAlgCl l →+* ℂ)
    (hψ : ψ ≠ 1) (D D' : WeilSheaf.LisseOnDenseOpen k₀ l)
    (hD : D.sheaf.IsIrreducibleLisse)
    (hne : D.sheaf.IsNonexceptional ψ D.j) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) (hFT : D.IsFourierPartner ψ D') :
    ∃ v : ℝ, D'.sheaf.IsPunctuallyPureOfWeight ι v := by
  sorry

end AlgebraicGeometry
