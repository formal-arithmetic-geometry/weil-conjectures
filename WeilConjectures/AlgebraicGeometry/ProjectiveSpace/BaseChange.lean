/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Projective space commutes with base change

For a morphism `g : X ⟶ S`, the projective space `ℙ(n; X)` is the base change of `ℙ(n; S)`
along `g` (`AlgebraicGeometry.ProjectiveSpace.isPullback_map`): both are base changes of the
integral model `ℙⁿ_ℤ`, and pullbacks paste. Consequently a morphism `T ⟶ ℙ(n; X)` is the same
as a morphism `T ⟶ X` together with a morphism `T ⟶ ℙ(n; S)` agreeing over `S`
(`AlgebraicGeometry.ProjectiveSpace.lift`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

variable (n : Type u) {X S : Scheme.{u}} (g : X ⟶ S)

/-- **Projective space commutes with base change**: the square
```
            map n g
  ℙ(n; X) ----------> ℙ(n; S)
     |                   |
     | ↘                 | ↘
     ↓                   ↓
     X ------- g ------> S
```
is cartesian. -/
lemma isPullback_map : IsPullback (map n g) (ℙ(n; X) ↘ X) (ℙ(n; S) ↘ S) g := by
  refine IsPullback.of_right (h₁₂ := toProjInt n S) (h₂₂ := terminal.from S)
    (v₁₃ := terminal.from _) ?_ (map_over n g) (isPullback_over_toProjInt n S).flip
  rw [map_toProjInt, terminal.comp_from]
  exact (isPullback_over_toProjInt n X).flip

variable {n g} {T : Scheme.{u}} (a : T ⟶ X) (b : T ⟶ ℙ(n; S)) (w : a ≫ g = b ≫ ℙ(n; S) ↘ S)

/-- A morphism `T ⟶ X` and a morphism `T ⟶ ℙ(n; S)` agreeing over `S` lift to `ℙ(n; X)`. -/
def lift : T ⟶ ℙ(n; X) :=
  (isPullback_map n g).lift b a w.symm

@[reassoc (attr := simp)]
lemma lift_over : lift a b w ≫ ℙ(n; X) ↘ X = a :=
  (isPullback_map n g).lift_snd _ _ _

@[reassoc (attr := simp)]
lemma lift_map : lift a b w ≫ map n g = b :=
  (isPullback_map n g).lift_fst _ _ _

/-- A morphism into `ℙ(n; X)` is determined by its composites with the structure morphism to
`X` and with `map n g : ℙ(n; X) ⟶ ℙ(n; S)`. -/
lemma hom_ext_of_map {f f' : T ⟶ ℙ(n; X)} (h₁ : f ≫ ℙ(n; X) ↘ X = f' ≫ ℙ(n; X) ↘ X)
    (h₂ : f ≫ map n g = f' ≫ map n g) : f = f' :=
  (isPullback_map n g).hom_ext h₂ h₁

end AlgebraicGeometry.ProjectiveSpace

end
