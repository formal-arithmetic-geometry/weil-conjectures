/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.RealSheaves

/-!
# Mixedness under extensions

An extension of mixed Weil sheaves is mixed
(`AlgebraicGeometry.WeilSheaf.IsMixed.of_shortExact`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {ι : PadicAlgCl l →+* ℂ}

/-- **Mixed extensions.** The middle term of a short exact sequence of Weil sheaves whose outer
terms are mixed is mixed. -/
theorem IsMixed.of_shortExact {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {S : ShortComplex (WeilSheaf k₀ l X)}
    (hS : S.ShortExact) (h₁ : S.X₁.IsMixed ι) (h₃ : S.X₃.IsMixed ι) : S.X₂.IsMixed ι :=
  let ⟨w₁, hw₁⟩ := h₁
  let ⟨w₃, hw₃⟩ := h₃
  ⟨max w₁ w₃, (hw₁.mono_weight (le_max_left _ _)).of_shortExact hS
    (hw₃.mono_weight (le_max_right _ _))⟩

end AlgebraicGeometry.WeilSheaf
