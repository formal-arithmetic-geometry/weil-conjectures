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
stays cartesian if the terminal object is replaced by any other terminal object, and deduce the
form of the base change lemma that applies over a terminal base.

## Main declarations

* `CategoryTheory.IsPullback.of_isTerminal`: transport of a cartesian square along a change of
  terminal objects at the tip of its cospan.
* `CategoryTheory.IsPullback.baseChange_pullback`: the fibre product over `S` of two base changes
  to `S` is the base change to `S` of the fibre product over `T`.
* `CategoryTheory.IsPullback.baseChange_prod`: the same statement over a terminal base `T`, where
  the legs of the cospans carry no information.
-/

@[expose] public section

namespace CategoryTheory.IsPullback

open Limits

variable {C : Type*} [Category* C]

/-- If a square over a terminal object `Z` is cartesian, then the square with the same projections
over any other terminal object `Z'` is cartesian. -/
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

/-- If `XS` and `YS` are base changes to `S` of `X` and `Y` along `s : S ⟶ T` and `W = XS ×[S] YS`,
then the two projections of `W` to `X` and `Y` agree over `T`. This is the compatibility needed to
map `W` to the fibre product `X ×[T] Y`. -/
theorem baseChange_w (hX : IsPullback a a' s p) (hY : IsPullback b b' s q)
    (hW : IsPullback u v a b) :
    (u ≫ a') ≫ p = (v ≫ b') ≫ q := by
  rw [Category.assoc, Category.assoc, ← hX.w, ← hY.w, ← Category.assoc, ← Category.assoc, hW.w]

/-- Base change preserves fibre products: if `XS` and `YS` are the base changes to `S` of `X` and
`Y` along `s : S ⟶ T`, if `W = XS ×[S] YS` and if `P = X ×[T] Y`, then `W` is the base change of
`P` to `S`.

This is the version for an arbitrary morphism `w : W ⟶ P` over `X` and `Y`; see
`CategoryTheory.IsPullback.baseChange_pullback` for the version where `w` is the morphism induced
by the universal property of `P`. -/
theorem baseChange_pullback' (hX : IsPullback a a' s p) (hY : IsPullback b b' s q)
    (hW : IsPullback u v a b) (hP : IsPullback c d p q) {w : W ⟶ P}
    (hwc : w ≫ c = u ≫ a') (hwd : w ≫ d = v ≫ b') :
    IsPullback (u ≫ a) w s (c ≫ p) := by
  have key : IsPullback w u c a' := by
    refine of_right ?_ hwc hP.flip
    rw [hwd, ← hX.w]
    exact hW.flip.paste_horiz hY.flip
  exact (key.paste_vert hX.flip).flip

/-- Base change preserves fibre products: if `XS` and `YS` are the base changes to `S` of `X` and
`Y` along `s : S ⟶ T`, if `W = XS ×[S] YS` and if `P = X ×[T] Y`, then `W` is the base change of
`P` to `S`.

The second projection of the resulting square is the morphism `W ⟶ P` induced by the universal
property of `P`; it is computed by the simp lemmas `CategoryTheory.IsPullback.lift_fst` and
`CategoryTheory.IsPullback.lift_snd`. -/
theorem baseChange_pullback (hX : IsPullback a a' s p) (hY : IsPullback b b' s q)
    (hW : IsPullback u v a b) (hP : IsPullback c d p q) :
    IsPullback (u ≫ a) (hP.lift (u ≫ a') (v ≫ b') (baseChange_w hX hY hW)) s (c ≫ p) :=
  baseChange_pullback' hX hY hW hP (hP.lift_fst ..) (hP.lift_snd ..)

/-- Base change from a terminal object preserves products: if `T` is terminal, if `XS` and `YS` are
the base changes to `S` of `X` and `Y`, if `W = XS ×[S] YS` and if `P = X × Y`, then `W` is the
base change of `P` to `S`.

The legs `s'` and `r` of the resulting cospan are arbitrary morphisms into an arbitrary terminal
object `T'`, so this applies to a caller whose squares are stated over `⊤_ C` as well as to one
whose squares are stated over some other terminal object. -/
theorem baseChange_prod {T' : C} (hT : IsTerminal T) (hT' : IsTerminal T')
    (hX : IsPullback a a' s p) (hY : IsPullback b b' s q) (hW : IsPullback u v a b)
    (hP : IsPullback c d p q) {s' : S ⟶ T'} {r : P ⟶ T'} :
    IsPullback (u ≫ a) (hP.lift (u ≫ a') (v ≫ b') (baseChange_w hX hY hW)) s' r :=
  (baseChange_pullback hX hY hW hP).of_isTerminal hT hT'

end BaseChange

end CategoryTheory.IsPullback
