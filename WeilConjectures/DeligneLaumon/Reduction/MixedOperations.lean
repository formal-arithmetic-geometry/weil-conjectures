/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.RealSheaves

/-!
# Mixedness under extensions and inverse images

Two of the closure properties of mixed Weil sheaves recorded in the blueprint proposition
`proposition-weights-under-usual-operations`:

* an extension of mixed Weil sheaves is mixed
  (`AlgebraicGeometry.WeilSheaf.IsMixed.of_shortExact`);
* the inverse image along any morphism of `k₀`-schemes locally of finite type preserves mixed
  upper weight bounds
  (`AlgebraicGeometry.WeilSheaf.isMixedOfWeightsAtMost_upperStar_obj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {ι : PadicAlgCl l →+* ℂ}

/-- **Mixed extensions.** The middle term of a short exact sequence of Weil sheaves whose outer
terms are mixed is mixed: both outer terms are mixed of weights at most the larger of their two
bounds. (blueprint: `proposition-weights-under-usual-operations--1`) -/
theorem IsMixed.of_shortExact {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {S : ShortComplex (WeilSheaf k₀ l X)}
    (hS : S.ShortExact) (h₁ : S.X₁.IsMixed ι) (h₃ : S.X₃.IsMixed ι) : S.X₂.IsMixed ι :=
  let ⟨w₁, hw₁⟩ := h₁
  let ⟨w₃, hw₃⟩ := h₃
  ⟨max w₁ w₃, (hw₁.mono_weight (le_max_left _ _)).of_shortExact hS
    (hw₃.mono_weight (le_max_right _ _))⟩

/-- **Upper bounds under inverse image.** Pulling back along any morphism `φ : X ⟶ Y` of
`k₀`-schemes locally of finite type carries Weil sheaves mixed of weights at most `w` to Weil
sheaves mixed of weights at most `w`; this is
`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.upperStar` in the notation of the blueprint
proposition. (blueprint: `proposition-weights-under-usual-operations--9`) -/
theorem isMixedOfWeightsAtMost_upperStar_obj {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l Y} {w : ℝ}
    (hF : F.IsMixedOfWeightsAtMost ι w) (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] :
    ((WeilSheaf.upperStar φ).obj F).IsMixedOfWeightsAtMost ι w :=
  hF.upperStar φ

end AlgebraicGeometry.WeilSheaf
