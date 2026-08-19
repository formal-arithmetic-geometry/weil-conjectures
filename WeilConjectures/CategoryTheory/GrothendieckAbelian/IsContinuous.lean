/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib

/-!

# Continuity of base change for the small sites (sorried)

Following the convention of the `SixFunctors` folder, the statement below is made for the
small sites defined by a general morphism property `P`, under the assumptions
`[P.IsMultiplicative]`, `[P.IsStableUnderBaseChange]` and `[P.HasOfPostcompProperty P]`;
all of them hold for `P = @Etale`.

## Sorried statement

- `CategoryTheory.GrothendieckTopology.isContinuous_overPullback`: base change along an
  *arbitrary* morphism is continuous for the small `Q`-topologies of `P`-schemes, for
  `Q ≤ P`. The inequality `hQP : Q ≤ P` is an explicit input, so this is a theorem
  rather than an instance; the definitions of the folder consume it through a local
  `have`. For `g` satisfying `P` continuity is proved
  (`CategoryTheory.GrothendieckTopology.isContinuous_overPullback_of_le` in
  `WeilConjectures.SixFunctors.LowerShriek.Defs`); in general it follows as in the étale
  case (`AlgebraicGeometry.Etale.isContinuous_overPullback` in
  `WeilConjectures.SixFunctors.UpperLowerStar.Etale`, which is proved): base change
  preserves covers because covers are jointly surjective families of `Q`-morphisms and
  `Q` is stable under base change, and it preserves compatible families because it is
  representably flat, the small site being finitely complete.

-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- Base change along an *arbitrary* morphism `g : W ⟶ U` is continuous for the small
`Q`-topologies of `P`-schemes, for `Q ≤ P`. For `g` satisfying `P` this is
`CategoryTheory.GrothendieckTopology.isContinuous_overPullback_of_le`; in general it is
proved as in the étale case (`AlgebraicGeometry.Etale.isContinuous_overPullback`): base
change preserves covers because covers are jointly surjective families of `Q`-morphisms
and `Q` is stable under base change, and it preserves compatible families because it is
representably flat, the small site being finitely complete.

The inequality `hQP : Q ≤ P` is an explicit input, so this is a theorem rather than an
instance; the definitions of the `SixFunctors` folder consume it through a local
`have`. -/
theorem isContinuous_overPullback (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
    (hQP : Q ≤ P) {W U : Scheme.{u}} (g : W ⟶ U) :
    (MorphismProperty.Over.pullback P ⊤ g).IsContinuous
      (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P)) :=
  sorry

end CategoryTheory.GrothendieckTopology
