/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Pullback squares of schemes along open immersions

In a pullback square of schemes whose bottom is an open immersion, the top is an open
immersion with range the preimage of the range of the bottom.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- In a pullback square of schemes whose bottom `g` is an open immersion, the range of the
top is the preimage under `f` of the range of `g`. -/
lemma _root_.CategoryTheory.IsPullback.opensRange_fst [IsOpenImmersion g]
    (h : IsPullback fst snd f g) :
    have : IsOpenImmersion fst := IsOpenImmersion.of_isPullback h.flip inferInstance
    fst.opensRange = f ⁻¹ᵁ g.opensRange := by
  ext
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨snd p, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h.w]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback _ y hy.symm
    have e : h.isoPullback.inv ≫ fst = Limits.pullback.fst f g := by
      rw [Iso.inv_comp_eq, h.isoPullback_hom_fst]
    exact ⟨h.isoPullback.inv p, by rwa [← Scheme.Hom.comp_apply, e]⟩

end AlgebraicGeometry
