/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Projective space commutes with base change

For a morphism `g : X ⟶ S`, the projective space `ℙ(n; X)` is the base change of `ℙ(n; S)`
along `g` (`AlgebraicGeometry.ProjectiveSpace.isPullback_map`): both are base changes of the
integral model `ℙⁿ_ℤ`, and pullbacks paste. Consequently a morphism `T ⟶ ℙ(n; X)` is the same
as a morphism `T ⟶ X` together with a morphism `T ⟶ ℙ(n; S)` agreeing over `S`
(`AlgebraicGeometry.ProjectiveSpace.lift`). Such a lift inherits from its second component
every property of morphisms that is stable under postcomposition with `ℙ(n; X) ⟶ ℙ(n; S)`;
this is spelled out for immersions and, `g` being separated, for closed immersions.

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.lift` — the morphism `T ⟶ ℙ(n; X)` induced by a morphism
  `T ⟶ X` and a morphism `T ⟶ ℙ(n; S)` agreeing over `S`.

## Main results

- `AlgebraicGeometry.ProjectiveSpace.isPullback_map` — `ℙ(n; X)` is the base change of
  `ℙ(n; S)` along `g : X ⟶ S`.
- `AlgebraicGeometry.ProjectiveSpace.map_of_isStableUnderBaseChange` and
  `AlgebraicGeometry.ProjectiveSpace.isSeparated_map` — a property of morphisms stable under
  base change passes from `g` to `map n g`; in particular `map n g` is separated if `g` is.
- `AlgebraicGeometry.ProjectiveSpace.isImmersion_lift` and
  `AlgebraicGeometry.ProjectiveSpace.isClosedImmersion_lift` — the lift of an immersion is an
  immersion, and the lift of a closed immersion along a separated `g` is a closed immersion.

## Blueprint

`isPullback_map` and `lift` describe `ℙ(n; X)` as `X ×_S ℙ(n; S)`, i.e. the base-change
projective space `def:nagata-projective-space-base-change`, and `isClosedImmersion_lift` is
the general form of `lemma:weil-pbc-chow-embedding-over-x` of the proper-base-change
blueprint.

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

/-- A property of morphisms that is stable under base change passes from `g : X ⟶ S` to its
base change `map n g : ℙ(n; X) ⟶ ℙ(n; S)`. -/
lemma map_of_isStableUnderBaseChange (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (hg : P g) : P (map n g) :=
  P.of_isPullback (isPullback_map n g).flip hg

/-- The base change `map n g : ℙ(n; X) ⟶ ℙ(n; S)` of a separated morphism `g` is separated. -/
instance isSeparated_map [IsSeparated g] : IsSeparated (map n g) :=
  map_of_isStableUnderBaseChange n g _ ‹_›

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

/-- The lift of an immersion `b : T ⟶ ℙ(n; S)` is an immersion:

```
        lift a b w
  T ----------------> ℙ(n; X)
    ╲                ╱
     b           map n g
      ╲            ╱
       ↘ ℙ(n; S) ↙
```

commutes. -/
instance isImmersion_lift [IsImmersion b] : IsImmersion (lift a b w) :=
  have : IsImmersion (lift a b w ≫ map n g) := by
    rw [lift_map]
    infer_instance
  .of_comp _ (map n g)

/-- The lift of a closed immersion `b : T ⟶ ℙ(n; S)` along a separated morphism `g` is a
closed immersion:

```
        lift a b w
  T ----------------> ℙ(n; X)
    ╲                ╱
     b           map n g
      ╲            ╱
       ↘ ℙ(n; S) ↙
```

commutes. -/
instance isClosedImmersion_lift [IsSeparated g] [IsClosedImmersion b] :
    IsClosedImmersion (lift a b w) :=
  -- `map n g` is separated, being a base change of `g`, and closed immersions cancel along
  -- separated morphisms.
  have : IsClosedImmersion (lift a b w ≫ map n g) := by
    rw [lift_map]
    infer_instance
  .of_comp _ (map n g)

/-- A morphism into `ℙ(n; X)` is determined by its composites with the structure morphism to
`X` and with `map n g : ℙ(n; X) ⟶ ℙ(n; S)`. -/
lemma hom_ext_of_map {f f' : T ⟶ ℙ(n; X)} (h₁ : f ≫ ℙ(n; X) ↘ X = f' ≫ ℙ(n; X) ↘ X)
    (h₂ : f ≫ map n g = f' ≫ map n g) : f = f' :=
  (isPullback_map n g).hom_ext h₂ h₁

end AlgebraicGeometry.ProjectiveSpace

end
