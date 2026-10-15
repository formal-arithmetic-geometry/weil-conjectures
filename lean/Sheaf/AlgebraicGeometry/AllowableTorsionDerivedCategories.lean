/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Sheaf.Paper.CohomologyInWeakSerreSubcategory
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Derived categories with allowable torsion

Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion).

The full subcategories are realized inside the unbounded derived category by intersection
with its bounded and bounded-below object properties. This gives the same full subcategories
as first passing to `D^b` or `D^+`. All coefficients here are abelian groups.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The allowable-torsion condition on an abelian etale sheaf: every geometric stalk element
has a positive annihilator with prime divisors in `P`. Nonprime members of `P` are irrelevant.
Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion). -/
def allowableTorsionSheafProperty (T : Scheme.{u}) (P : Set ℕ) :
    ObjectProperty (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  fun F ↦ ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T)
    (x : ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj F),
    ∃ n : ℕ, 0 < n ∧ (∀ p : ℕ, p.Prime → p ∣ n → p ∈ P) ∧ n • x = 0

/-- Bounded-below objects with allowable-torsion cohomology, viewed in `D(T_et)`.
Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion). -/
def allowableTorsionPlusProperty (T : Scheme.{u}) (P : Set ℕ) :
    ObjectProperty (DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
  DerivedCategory.homologyProperty (allowableTorsionSheafProperty T P) ⊓
    DerivedCategory.TStructure.t.plus

/-- Bounded objects with allowable-torsion cohomology, viewed in `D(T_et)`.
Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion). -/
def allowableTorsionBoundedProperty (T : Scheme.{u}) (P : Set ℕ) :
    ObjectProperty (DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
  DerivedCategory.homologyProperty (allowableTorsionSheafProperty T P) ⊓
    DerivedCategory.TStructure.t.bounded

/-- Strict fullness of the bounded-below allowable-torsion class.
Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion).
Proof: an isomorphism induces isomorphisms on all cohomology sheaves and their geometric
stalks. Transport each positive annihilator across these additive isomorphisms.
The bounded-below condition is invariant under isomorphisms by the standard t-structure. -/
@[instance] theorem allowableTorsionPlusProperty_isClosedUnderIsomorphisms
    (T : Scheme.{u}) (P : Set ℕ) :
    (allowableTorsionPlusProperty T P).IsClosedUnderIsomorphisms := by
  sorry

/-- Strict fullness of the bounded allowable-torsion class.
Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion).
Proof: isomorphisms preserve cohomology and geometric stalks, hence each positive allowable
annihilator. The bounded condition is invariant under isomorphisms. -/
@[instance] theorem allowableTorsionBoundedProperty_isClosedUnderIsomorphisms
    (T : Scheme.{u}) (P : Set ℕ) :
    (allowableTorsionBoundedProperty T P).IsClosedUnderIsomorphisms := by
  sorry

/-- The bounded-below allowable-torsion class inherits its triangulated structure.
Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion).
Proof: zero has annihilator 1. Subgroups and quotients inherit allowable annihilators.
In an extension, kill the image of an element by an allowable n, then kill its lift in
the subgroup by an allowable m. Their product mn kills the original element and has
only allowable prime factors. Exactness of geometric stalks
(`prop-weil-pbc-geometric-stalks-exact`, finite-limit preservation and the skyscraper
adjunction) therefore makes allowable-torsion sheaves a weak Serre class.
Apply `cohomology_in_weak_serre_subcategory` to this class and take its bounded-below
intersection clause (`lem-sbc-cohomology-in-weak-serre-subcategory`). -/
@[instance] theorem allowableTorsionPlusProperty_isTriangulated
    (T : Scheme.{u}) (P : Set ℕ) :
    (allowableTorsionPlusProperty T P).IsTriangulated := by
  sorry

/-- The bounded allowable-torsion class inherits its triangulated structure.
Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion).
Proof: zero is killed by 1; kernels and cokernels inherit allowable annihilators stalkwise.
For an extension, annihilators n of the image and m of the resulting subgroup element
multiply to an allowable annihilator mn. Exactness of geometric stalks
(`prop-weil-pbc-geometric-stalks-exact`) gives weak Serre closure for the sheaf class.
Apply the bounded intersection clause of `cohomology_in_weak_serre_subcategory`
(`lem-sbc-cohomology-in-weak-serre-subcategory`). -/
@[instance] theorem allowableTorsionBoundedProperty_isTriangulated
    (T : Scheme.{u}) (P : Set ℕ) :
    (allowableTorsionBoundedProperty T P).IsTriangulated := by
  sorry

/-- `D^+_{P-tor}(T_et)`, with the inherited shifts and distinguished triangles.
Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion). -/
abbrev AbelianDerivedCategoryPlusTorsionOfPrimes (T : Scheme.{u}) (P : Set ℕ) : Type _ :=
  (allowableTorsionPlusProperty T P).FullSubcategory

/-- `D^b_{P-tor}(T_et)`, with the inherited shifts and distinguished triangles.
Source: blueprint `sec-smooth-base-change/sk-rem-rest/`
`sbc-def-derived-categories-with-allowable-torsion.md`
(blueprint: sbc-def-derived-categories-with-allowable-torsion). -/
abbrev AbelianDerivedCategoryBoundedTorsionOfPrimes (T : Scheme.{u}) (P : Set ℕ) : Type _ :=
  (allowableTorsionBoundedProperty T P).FullSubcategory

end AlgebraicGeometry.Etale
