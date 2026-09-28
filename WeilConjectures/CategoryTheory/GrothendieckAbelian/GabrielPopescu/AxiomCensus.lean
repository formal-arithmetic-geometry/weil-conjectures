/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu

/-!

# Axiom census for the presentability of separators

`WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu`
proves that a separator of a Grothendieck abelian category is `κ`-presentable for a large
enough regular cardinal `κ`, through the presentability of small modules proved in
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.FilteredColimits`. This file records
`#print axioms` checks for these results; they are run by the build, so a `sorry` appearing in
their transitive dependencies breaks compilation rather than going unnoticed.

The checks are here rather than in the Mathlib mirror files because `#print axioms` is a
diagnostic command; this file has no mathematical content and is a leaf of the import graph.

-/

@[expose] public section

/--
info: 'ModuleCat.isCardinalPresentable_of_hasCardinalLT' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.isCardinalPresentable_of_hasCardinalLT

/--
info: 'CategoryTheory.IsGrothendieckAbelian.isCardinalPresentable_of_isSeparator' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.IsGrothendieckAbelian.isCardinalPresentable_of_isSeparator

/--
info: 'CategoryTheory.IsGrothendieckAbelian.exists_isCardinalPresentable_of_isSeparator' depends
  on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.IsGrothendieckAbelian.exists_isCardinalPresentable_of_isSeparator
