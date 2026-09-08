/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Base change of a fibre product

Base change preserves fibre products: if `XS = S ×[T] X` and `YS = S ×[T] Y`, then
`XS ×[S] YS = S ×[T] (X ×[T] Y)`. This is `CategoryTheory.IsPullback.baseChange_pullback`, stated
purely in terms of cartesian squares so that no `HasPullback` instances are needed and it composes
with the rest of the pasting API.

We also record that a cartesian square whose cospan is a pair of morphisms to a terminal object
stays cartesian if the terminal object is replaced by any other terminal object.

## Main declarations

* `CategoryTheory.IsPullback.of_isTerminal`: transport of a cartesian square along a change of
  terminal objects at the tip of its cospan.
* `CategoryTheory.IsPullback.baseChange_pullback`: the fibre product over `S` of two base changes
  to `S` is the base change to `S` of the fibre product over `T`.
-/

@[expose] public section

namespace CategoryTheory.IsPullback

open Limits

variable {C : Type*} [Category* C]

/-- If a square over a terminal object `Z` is cartesian, then the square with the same projections
over any other terminal object `Z'` is cartesian:

```
  P --fst--> X          P --fst--> X
  |          |          |          |
 snd         f   ⟹     snd        f'
  ↓          ↓          ↓          ↓
  Y ---g---> Z          Y ---g'--> Z'
```
-/
theorem of_isTerminal {P X Y Z Z' : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (hZ : IsTerminal Z) {f' : X ⟶ Z'} {g' : Y ⟶ Z'}
    (hZ' : IsTerminal Z') :
    IsPullback fst snd f' g' :=
  mk' (hZ'.hom_ext _ _) (fun _ _ _ h₁ h₂ ↦ h.hom_ext h₁ h₂)
    (fun _ a b _ ↦ ⟨h.lift a b (hZ.hom_ext _ _), h.lift_fst .., h.lift_snd ..⟩)

section BaseChange

variable {T S X Y XS YS W P : C} {s : S ⟶ T} {p : X ⟶ T} {q : Y ⟶ T}
  {a : XS ⟶ S} {a' : XS ⟶ X} {b : YS ⟶ S} {b' : YS ⟶ Y}
  {u : W ⟶ XS} {v : W ⟶ YS} {c : P ⟶ X} {d : P ⟶ Y}

/-- Base change preserves fibre products: if `XS` and `YS` are the base changes to `S` of `X` and
`Y` along `s : S ⟶ T`, if `W = XS ×[S] YS` and if `P = X ×[T] Y`, then `W` is the base change of
`P` to `S`. The four squares involved are

```
  XS --a'-> X       YS --b'-> Y       W --v--> YS       P --d--> Y
  |         |       |         |       |        |        |        |
  a         p       b         q       u        b        c        q
  ↓         ↓       ↓         ↓       ↓        ↓        ↓        ↓
  S ---s--> T       S ---s--> T       XS --a-> S        X --p--> T
```

and the conclusion is that

```
  W ----w----> P
  |            |
 u ≫ a        c ≫ p
  ↓            ↓
  S ----s----> T
```

is cartesian, for any `w : W ⟶ P` over `X` and `Y`. -/
theorem baseChange_pullback (hX : IsPullback a a' s p) (hY : IsPullback b b' s q)
    (hW : IsPullback u v a b) (hP : IsPullback c d p q) {w : W ⟶ P}
    (hwc : w ≫ c = u ≫ a') (hwd : w ≫ d = v ≫ b') :
    IsPullback (u ≫ a) w s (c ≫ p) := by
  -- `W` is the fibre product of `P` and `XS` over `X`, and pasting that square onto `hX`
  -- gives the claim
  have key : IsPullback w u c a' := by
    refine of_right ?_ hwc hP.flip
    rw [hwd, ← hX.w]
    exact hW.flip.paste_horiz hY.flip
  exact (key.paste_vert hX.flip).flip

end BaseChange

end CategoryTheory.IsPullback
