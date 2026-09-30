/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!

# Axiom census for the open–closed exact sequence

For the coefficient category `ModuleCat.{u + 1} Λ` of modules over a ring `Λ : Type (u + 1)`
every hypothesis on the coefficients of `WeilConjectures.SixFunctors.OpenClosed.Exact` is
inferred: `CategoryTheory.HasSmallSiteSheafify` from
`WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients`, the rest from
Mathlib. This file records that specialization together with a `#print axioms` check, and
does the same for the four other statements of the chapter. The checks are run by the
build, so a change in the axiom dependencies beneath these declarations breaks compilation
rather than going unnoticed.

All six declarations depend only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. Sheafification in the definition of `AlgebraicGeometry.Etale.upperStar` is
discharged by the instance `CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall`
of `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`, which is proved through
the transfinite plus construction; these checks guard against a `sorry` re-entering beneath
the chapter.

Note that the census for the `ModuleCat` specialization also covers the instances used to
discharge the coefficient hypotheses, which the censuses of the general statements do not.

This file has no mathematical content; it is a leaf of the import graph, so that the
concrete coefficient categories are not pulled into the files above.

## Main results

- `AlgebraicGeometry.Etale.shortExact_openClosedShortComplex_moduleCat`: the open–closed
  short complex is short exact for sheaves of `Λ`-modules
  (blueprint: `thm:openclosed-exact`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable {U Z X : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]

/-- **The open–closed short complex is short exact**, for sheaves of `Λ`-modules: the
specialization of `AlgebraicGeometry.Etale.shortExact_openClosedShortComplex` at
`A = ModuleCat.{u + 1} Λ`, where every hypothesis on the coefficient category is inferred.
It has no content beyond that statement; it is stated separately so that the `#print axioms`
check below is run by the build. -/
theorem Etale.shortExact_openClosedShortComplex_moduleCat (Λ : Type (u + 1)) [Ring Λ]
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    (Etale.openClosedShortComplex (ModuleCat.{u + 1} Λ) j i
      (disjoint_range_of_range_eq_compl j i hij) M).ShortExact :=
  Etale.shortExact_openClosedShortComplex _ j i M hij

/--
info: 'AlgebraicGeometry.Etale.shortExact_openClosedShortComplex_moduleCat' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Etale.shortExact_openClosedShortComplex_moduleCat

/--
info: 'AlgebraicGeometry.Etale.isZero_upperStar_lowerStar_of_disjoint_range' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Etale.isZero_upperStar_lowerStar_of_disjoint_range

/--
info: 'AlgebraicGeometry.Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range

/--
info: 'AlgebraicGeometry.Etale.upperStarCompSheafFiberIso' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Etale.upperStarCompSheafFiberIso

/--
info: 'AlgebraicGeometry.Etale.isIso_upperStarLowerStarAdjunction_counit' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Etale.isIso_upperStarLowerStarAdjunction_counit

/--
info: 'AlgebraicGeometry.Etale.jointlyReflectIsomorphisms_upperStar' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Etale.jointlyReflectIsomorphisms_upperStar

/-! ### Smoke tests for the coefficient hypotheses

That the sheaf categories with these coefficients are Grothendieck abelian is what the
derived-category files consume; here it is checked to be inferable. -/

variable (Λ : Type (u + 1)) [Ring Λ]

example : IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  inferInstance

example : IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  inferInstance

end AlgebraicGeometry
