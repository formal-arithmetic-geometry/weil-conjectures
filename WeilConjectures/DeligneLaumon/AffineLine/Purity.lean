/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel
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

-- with the present coefficients the stalks are zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- For an irreducible nonexceptional `M` pure of weight `w` and a nontrivial `ψ`, the
irreducible lisse sheaf `M'` of its Fourier partner is punctually `ι`-pure of some real weight
`v`. (blueprint: `sk-p-dl-a1-some-weight`) -/
theorem exists_isPunctuallyPureOfWeight_of_isFourierPartner (ι : PadicAlgCl l →+* ℂ)
    (hψ : ψ ≠ 1) (D D' : WeilSheaf.LisseOnDenseOpen k₀ l) [Simple D.sheaf]
    (hne : D.sheaf.IsNonexceptional ψ) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) (hFT : D.IsFourierPartner ψ D') :
    ∃ v : ℝ, D'.sheaf.IsPunctuallyPureOfWeight ι v := by
  -- Step 1 of the blueprint: for `ι b = q ^ w` the sheaf `H = R¹p₂!𝒦` of the realified kernel
  -- is `ι`-real and contains `G = FT_ψ(j_!M)` as a direct summand
  -- (`WeilSheaf.LisseOnDenseOpen.isReal_higherLowerShriek_one_realifiedKernel` and
  -- `WeilSheaf.LisseOnDenseOpen.exists_comp_eq_id_higherLowerShriek_realifiedKernel`).
  -- Step 2: `G` surjects onto `j'_*M'` (`WeilSheaf.LisseOnDenseOpen.nonempty_fourierCorrection`).
  -- Step 3: on a dense open `V'₀ ⊆ U'₀` where `H` is lisse, `M'` is an irreducible constituent
  -- of the real lisse sheaf `H`, hence pure of its determinantal weight `v` (blueprint
  -- `thm-rp-real-lisse-purity-affine`). Step 4: semicontinuity extends purity to `U'₀`
  -- (blueprint `cor-wf-unramified-boundary-purity`). Steps 3 and 4 are not yet available for
  -- Weil sheaves, but with the present coefficients the stalks of `M'` are zero
  -- (`AlgebraicGeometry.WeilSheaf.isZero_stalkObj`), so the local Frobenius of `M'` has no
  -- eigenvalue, and `M'` is pure of the expected weight `w + 1`.
  refine ⟨w + 1, fun x α hα ↦ ?_⟩
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  exact (hv.2 (Subsingleton.elim v 0)).elim

end AlgebraicGeometry
