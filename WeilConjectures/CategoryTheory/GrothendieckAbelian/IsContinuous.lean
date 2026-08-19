/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder

/-!

# Continuity of base change for the small sites (sorried)

Base change along an arbitrary morphism is continuous for the small `Q`-topologies of
`P`-schemes, for `Q ≤ P`: it preserves covers because covers are jointly surjective
families of `Q`-morphisms and `Q` is stable under base change, and it preserves
compatible families because it is representably flat, the small site being finitely
complete.

## No smallness hypothesis

Unlike the sorried statements of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf` and
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`, this one needs
no smallness input: both halves of `Functor.IsContinuous` are conditions on individual
covering sieves and individual compatible families. Cover-preservation only uses that
covers are jointly surjective families of `Q`-morphisms and that `Q` is stable under base
change, and compatible-family-preservation only uses representable flatness of base
change, which holds because the small site is finitely complete. Neither quantifies over
the objects of the site, so the statement is correct as it stands for an arbitrary `P`
satisfying the multiplicativity-type hypotheses below.

-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

/-- Base change along an *arbitrary* morphism `g : W ⟶ U` is continuous for the small
`Q`-topologies of `P`-schemes, for `Q ≤ P`: it preserves covers because covers are
jointly surjective families of `Q`-morphisms and `Q` is stable under base change, and it
preserves compatible families because it is representably flat, the small site being
finitely complete. -/
theorem isContinuous_overPullback (P Q : MorphismProperty Scheme.{u})
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
    (hQP : Q ≤ P) {W U : Scheme.{u}} (g : W ⟶ U) :
    (MorphismProperty.Over.pullback P ⊤ g).IsContinuous
      (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P)) :=
  sorry

end CategoryTheory.GrothendieckTopology
