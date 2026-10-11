/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.OpenLine

/-!
# The curve estimate on an arbitrary affine curve

Let `C` be an affine `k₀`-scheme of finite type of dimension at most one, not necessarily
geometrically connected, and `F` a Weil sheaf on `C`, punctually `ι`-pure of weight `w`. Then
`H_c^r(C, F)` has weights at most `w + r`.

## Implementation notes

The blueprint (`lem-zl-relative-curve-punctual`, `lem-zl-affine-curve-hc2-purity`) passes to a
finite constant extension over which the geometric components of `C` are defined. We avoid
constant extensions: a finite morphism `f : C ⟶ 𝔸¹_{k₀}` (Noether normalization) identifies
`H_c^r(C, F)` with `H_c^r(𝔸¹, f₀*F)`; the finite direct image `f₀*F` is punctually pure of weight
`w` and lisse on a dense open `V ⊆ 𝔸¹`, which is a smooth geometrically connected curve, where the
curve estimate `thm-a1-curve-upper` applies; the finite complement contributes only in degree
zero, with weights at most `w`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (ι : PadicAlgCl l →+* ℂ)

/-- **The curve estimate on an affine curve.** Let `C` be an affine `k₀`-scheme of finite type of
dimension at most one and `F` a Weil sheaf on `C`, punctually `ι`-pure of weight `w`. Then
`H_c^r(C, F)` has weights at most `w + r` (blueprint: `lem-zl-relative-curve-punctual`, the curve
estimate on the geometric components of an affine fibre). -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_of_isAffine {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    (hC : ringKrullDim Γ(C, ⊤) ≤ 1) (F : WeilSheaf k₀ l C) {w : ℝ}
    (hw : F.IsPunctuallyPureOfWeight ι w) (r : ℤ) :
    (F.compactlySupportedCohomology r).HasWeightsAtMostOver k₀ ι (w + r) := by
  sorry

end AlgebraicGeometry
