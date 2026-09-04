/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Pullback squares of schemes along open immersions

In a pullback square of schemes whose bottom is an open immersion, the top is an open
immersion with range the preimage of the range of the bottom.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- In a pullback square of schemes whose bottom is an open immersion, the top is an open
immersion. -/
lemma _root_.CategoryTheory.IsPullback.isOpenImmersion_fst [IsOpenImmersion g]
    (h : IsPullback fst snd f g) : IsOpenImmersion fst :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip inferInstance

/-- In a pullback square of schemes whose bottom `g` is an open immersion, the range of the
top is the preimage under `f` of the range of `g`. -/
lemma _root_.CategoryTheory.IsPullback.opensRange_fst [IsOpenImmersion g]
    (h : IsPullback fst snd f g) :
    have : IsOpenImmersion fst := h.isOpenImmersion_fst
    fst.opensRange = f ⁻¹ᵁ g.opensRange := by
  have : IsOpenImmersion fst := h.isOpenImmersion_fst
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨snd p, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h.w]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨p, hp, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    have e : h.isoPullback.inv ≫ fst = Limits.pullback.fst f g := by
      rw [Iso.inv_comp_eq, h.isoPullback_hom_fst]
    exact ⟨h.isoPullback.inv p, by rw [← Scheme.Hom.comp_apply, e]; exact hp⟩

end AlgebraicGeometry
