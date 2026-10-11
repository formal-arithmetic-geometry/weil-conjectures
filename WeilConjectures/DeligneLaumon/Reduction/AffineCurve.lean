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

/-- **Purity of the top affine-curve factor.** Let `C` be a smooth affine curve over `k₀`, not
necessarily geometrically connected, and let `E` be a lisse Weil sheaf on `C`, punctually `ι`-pure
of weight `0`. Then `H_c^2(C, E)` is `ι`-pure of weight `2` (blueprint:
`lem-zl-affine-curve-hc2-purity`). For a finite morphism `f : C ⟶ 𝔸¹_{k₀}`,
`H_c^2(C, E) ≅ H_c^2(𝔸¹, f₀*E) ≅ H_c^2(V, f₀*E)` for a dense open `V ⊆ 𝔸¹` on which `f₀*E` is
lisse, and the degree-two endpoint estimate applies on the geometrically connected `V`. -/
theorem isPureOfWeightOver_compactlySupportedCohomology_two_of_isAffine {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))] (E : WeilSheaf k₀ l C)
    (hE : E.IsLisse) (hpure : E.IsPunctuallyPureOfWeight ι 0) :
    -- `C ↘ Spec k₀` is locally of finite type, being smooth
    haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
    (E.compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι 2 := by
  sorry

/-- **Vanishing of `H_c^0` on a smooth affine curve.** Let `C` be a smooth affine curve over `k₀`,
not necessarily geometrically connected, and let `E` be a lisse Weil sheaf on `C`. Then
`H_c^0(C, E) = 0` (blueprint: `lem-zl-relative-envelope-factor-reality`, the vanishing of the
degree-zero group of an affine fibre, by `lem-a1-affine-hc0`). For a finite morphism
`f : C ⟶ 𝔸¹_{k₀}`, the direct image `f₀*E` is the middle extension of its restriction to a dense
open `V ⊆ 𝔸¹` on which it is lisse (`lem-a1-lisse-middle-extension`), and `H_c^0` of a middle
extension on the geometrically connected `𝔸¹` vanishes. -/
theorem WeilSheaf.subsingleton_compactlySupportedCohomology_zero_of_isAffine {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))] (E : WeilSheaf k₀ l C)
    (hE : E.IsLisse) :
    -- `C ↘ Spec k₀` is locally of finite type, being smooth
    haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
    Subsingleton (E.compactlySupportedCohomology 0).carrier := by
  sorry

end AlgebraicGeometry
