/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Equalizers as pullbacks of the diagonal

For two morphisms `f g : T ⟶ X` over `S`, the equalizer of `f` and `g` is the pullback of
`(f, g) : C ⟶ X ×_S X` along the diagonal of `X ⟶ S`:

- `CategoryTheory.Limits.isPullback_equalizer_ι_diagonal`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {T X S : C} {p : X ⟶ S} [HasPullback p p]
  (f g : T ⟶ X) [HasEqualizer f g] (h : f ≫ p = g ≫ p)

/-- The equalizer of `f g : T ⟶ X` over `S` is the pullback of `(f, g) : T ⟶ X ×_S X` along
the diagonal:

```
  equalizer f g ──ι──▶ T
        │              │
     ι ≫ f             │ (f, g)
        ▼              ▼
        X ─────Δ─────▶ X ×_S X
```

is Cartesian. -/
lemma isPullback_equalizer_ι_diagonal :
    IsPullback (equalizer.ι f g) (equalizer.ι f g ≫ f) (pullback.lift f g h)
      (pullback.diagonal p) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (by apply pullback.hom_ext <;> simp [equalizer.condition f g])
    (fun t ↦ equalizer.lift t.fst ?_)
    (fun t ↦ equalizer.lift_ι _ _) (fun t ↦ ?_)
    (fun t m h₁ _ ↦ equalizer.hom_ext (by simpa using h₁)))
  all_goals
    have h₁ := t.condition =≫ pullback.fst p p
    have h₂ := t.condition =≫ pullback.snd p p
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
      pullback.diagonal_snd] at h₁ h₂
  · rw [h₁, h₂]
  · simp [h₁]

end CategoryTheory.Limits
