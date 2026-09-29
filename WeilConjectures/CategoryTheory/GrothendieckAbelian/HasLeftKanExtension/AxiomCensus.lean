/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Christian Merten
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension

/-!

# Axiom census for the left Kan extensions along base change

The base-change half of `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`
rests entirely on two instances: the pointwise left Kan extensions along the opposite of base
change exist, by the general
`WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise`, and are left exact for
a Grothendieck abelian coefficient category, by
`WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty`. Both are proved, and the
pullback `AlgebraicGeometry.Etale.upperStar` and its pro-étale counterpart are defined through
them. This file records `#print axioms`
checks for the two; they are run by the build, so a `sorry` reappearing anywhere in the
transitive dependencies of these declarations breaks compilation rather than going
unnoticed.

The checks are here rather than in the files that state or use the instances because
`#print axioms` is a diagnostic command; this file has no mathematical content and is a leaf
of the import graph.

-/

@[expose] public section

/--
info: 'CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_hasColimitsOfSize

/--
info: 'CategoryTheory.MorphismProperty.Over.preservesFiniteLimits_op_lan_pullback' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.MorphismProperty.Over.preservesFiniteLimits_op_lan_pullback
