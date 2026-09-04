/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Complements on pullback squares

If only the first leg of a cospan is changed, the induced morphism of pullbacks is a base
change of the morphism of legs (`CategoryTheory.Limits.isPullback_pullback_map_left`). We
also record that a pullback square can be cancelled against a monomorphism
(`CategoryTheory.IsPullback.comp_mono_iff`) and that two morphisms into the corner of a
pullback square agree as soon as their composites with both legs do
(`CategoryTheory.IsPullback.fst_comp_eq_snd_comp`).
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [HasPullbacks C]

/-- **A morphism of the first leg of a cospan induces a base-change square on pullbacks.**
For a cospan `A --m--> B --p--> T <--π-- S`, the square

```
  A ×_T S --pullback.map--> B ×_T S
     |                         |
    fst                       fst
     |                         |
     v                         v
     A ----------m---------->  B
```

is a pullback square. -/
lemma isPullback_pullback_map_left {A B T S : C} (m : A ⟶ B) (p : B ⟶ T) (π : S ⟶ T) :
    IsPullback (pullback.fst (m ≫ p) π)
      (pullback.map (m ≫ p) π p π m (𝟙 S) (𝟙 T) (by simp) (by simp)) m (pullback.fst p π) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback p π)
  have h : pullback.map (m ≫ p) π p π m (𝟙 S) (𝟙 T) (by simp) (by simp) ≫ pullback.snd p π =
      pullback.snd (m ≫ p) π := by simp
  rw [h]
  exact IsPullback.of_hasPullback (m ≫ p) π

end CategoryTheory.Limits

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
