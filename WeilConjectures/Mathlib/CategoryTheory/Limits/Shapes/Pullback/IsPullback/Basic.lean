/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Complements on pullback squares

We record that a commutative square can be cancelled against a monomorphism
(`CategoryTheory.IsPullback.comp_mono_iff`) and that two morphisms out of the legs of a
pullback square agree on the chosen pullback as soon as their composites with the legs of a
realization of the square agree (`CategoryTheory.IsPullback.fst_comp_eq_snd_comp`).
-/

@[expose] public section

namespace CategoryTheory.IsPullback

variable {C : Type*} [Category C]

/-- **Cancelling a monomorphism out of a commutative square.** For a monomorphism
`j : Z ⟶ Z'`, the outer square

```
  P ---q---> T
  |          |
  p          β
  |          |
  v          v
  S ---α---> Z ---j---> Z'
```

is a pullback square if and only if the inner square `p, q, α, β` is. -/
lemma comp_mono_iff {P S T Z Z' : C} {p : P ⟶ S} {q : P ⟶ T} {α : S ⟶ Z} {β : T ⟶ Z}
    (j : Z ⟶ Z') [Mono j] :
    IsPullback p q (α ≫ j) (β ≫ j) ↔ IsPullback p q α β := by
  have hw {D : C} (a : D ⟶ S) (b : D ⟶ T) : a ≫ α ≫ j = b ≫ β ≫ j ↔ a ≫ α = b ≫ β := by
    rw [← Category.assoc, ← Category.assoc, cancel_mono]
  constructor
  · intro h
    refine IsPullback.of_isLimit' ⟨(hw p q).mp h.w⟩
      (Limits.PullbackCone.IsLimit.mk _ (fun s ↦ h.lift s.fst s.snd
        ((hw s.fst s.snd).mpr s.condition)) (fun s ↦ h.lift_fst _ _ _)
        (fun s ↦ h.lift_snd _ _ _) fun s m h₁ h₂ ↦ h.hom_ext ?_ ?_)
    · rw [h₁, h.lift_fst]
    · rw [h₂, h.lift_snd]
  · intro h
    refine IsPullback.of_isLimit' ⟨(hw p q).mpr h.w⟩
      (Limits.PullbackCone.IsLimit.mk _ (fun s ↦ h.lift s.fst s.snd
        ((hw s.fst s.snd).mp s.condition)) (fun s ↦ h.lift_fst _ _ _)
        (fun s ↦ h.lift_snd _ _ _) fun s m h₁ h₂ ↦ h.hom_ext ?_ ?_)
    · rw [h₁, h.lift_fst]
    · rw [h₂, h.lift_snd]

/-- **Two morphisms out of the legs of a pullback square that agree on a realization of the
square agree on the chosen pullback.** Given

```
  P ---q---> T ---w---> Y
  |          |
  p          β
  |          |
  v          v
  S ---α---> Z
```

with `S ---v---> Y` and `p ≫ v = q ≫ w`, one has
`pullback.fst α β ≫ v = pullback.snd α β ≫ w`. -/
lemma fst_comp_eq_snd_comp {P S T Z : C} {p : P ⟶ S} {q : P ⟶ T} {α : S ⟶ Z} {β : T ⟶ Z}
    (h : IsPullback p q α β) [Limits.HasPullback α β] {Y : C} (v : S ⟶ Y) (w : T ⟶ Y)
    (hvw : p ≫ v = q ≫ w) :
    Limits.pullback.fst α β ≫ v = Limits.pullback.snd α β ≫ w := by
  rw [← cancel_epi h.isoPullback.hom, ← Category.assoc, ← Category.assoc,
    h.isoPullback_hom_fst, h.isoPullback_hom_snd, hvw]

end CategoryTheory.IsPullback
