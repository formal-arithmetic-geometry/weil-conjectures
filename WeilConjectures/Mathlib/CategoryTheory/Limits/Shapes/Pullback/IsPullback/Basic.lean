/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!

# Base change along the first projection of a fibre product

For `j : U ⟶ X` and morphisms `f : X ⟶ S`, `g : Y ⟶ S`, the induced morphism
`U ×_S Y ⟶ X ×_S Y` is a base change of `j` along the first projection `X ×_S Y ⟶ X`.

## Main definitions and results

- `CategoryTheory.Limits.pullbackCompFstMap`: the morphism `U ×_S Y ⟶ X ×_S Y`;
- `CategoryTheory.Limits.isPullback_pullbackCompFstMap`: it is a base change of `j`.

Mathlib records the same cartesian square in isomorphism form, as
`CategoryTheory.Limits.pullbackRightPullbackFstIso`, which identifies
`U ×_X (X ×_S Y)` with `U ×_S Y`.

-/

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {S X Y U : C} (f : X ⟶ S) (g : Y ⟶ S) (j : U ⟶ X)
  [HasPullback f g] [HasPullback (j ≫ f) g]

/-- The base change of `j : U ⟶ X` along the first projection `X ×_S Y ⟶ X`, as a
morphism `U ×_S Y ⟶ X ×_S Y`. -/
def pullbackCompFstMap : pullback (j ≫ f) g ⟶ pullback f g :=
  pullback.map (j ≫ f) g f g j (𝟙 Y) (𝟙 S) (by simp) (by simp)

@[reassoc (attr := simp)]
lemma pullbackCompFstMap_fst :
    pullbackCompFstMap f g j ≫ pullback.fst f g = pullback.fst (j ≫ f) g ≫ j := by
  simp [pullbackCompFstMap]

@[reassoc (attr := simp)]
lemma pullbackCompFstMap_snd :
    pullbackCompFstMap f g j ≫ pullback.snd f g = pullback.snd (j ≫ f) g := by
  simp [pullbackCompFstMap]

/-- **The base-changed square is cartesian**: `U ×_S Y` is the fibre product of
`j : U ⟶ X` and the first projection `X ×_S Y ⟶ X`, i.e. the square

```
U ×_S Y --pullbackCompFstMap--> X ×_S Y
   |                               |
pullback.fst                  pullback.fst
   ↓                               ↓
   U ------------- j ----------->  X
```

is a pullback square. -/
lemma isPullback_pullbackCompFstMap :
    IsPullback (pullbackCompFstMap f g j) (pullback.fst (j ≫ f) g)
      (pullback.fst f g) j :=
  IsPullback.of_right (by simpa using (IsPullback.of_hasPullback (j ≫ f) g).flip)
    (pullbackCompFstMap_fst f g j) (IsPullback.of_hasPullback f g).flip

end CategoryTheory.Limits
