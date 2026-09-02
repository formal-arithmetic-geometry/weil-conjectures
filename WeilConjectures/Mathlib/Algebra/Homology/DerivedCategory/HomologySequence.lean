/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# Complexes with homology in a weak Serre class

Given a property `P` of objects of an abelian category `A`, the objects of the derived
category `D(A)` all of whose homology objects satisfy `P` form the property
`DerivedCategory.hasHomologyIn P`, the specialisation of
`CategoryTheory.Functor.hasHomologyIn` to the homology functors of `D(A)`.

## Main definitions

* `DerivedCategory.hasHomologyIn`: the objects of `D(A)` whose homology all satisfies `P`.

## Main results

* `DerivedCategory.hasHomologyIn_isTriangulated`: for a weak Serre class `P`, the complexes
  with homology in `P` form a triangulated subcategory of `D(A)`.

## References

* [Stacks 06UQ], Derived Categories, Lemma 13.17.1.

-/

@[expose] public section

universe w v u

open CategoryTheory

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  (P : ObjectProperty A)

/-- The objects of the derived category all of whose homology objects satisfy `P`. -/
noncomputable def hasHomologyIn : ObjectProperty (DerivedCategory A) :=
  (homologyFunctor A 0).hasHomologyIn P

/-- An object of the derived category has homology in `P` if and only if all its homology
objects `Hⁿ` satisfy `P`. -/
lemma hasHomologyIn_iff (M : DerivedCategory A) :
    hasHomologyIn P M ↔ ∀ n : ℤ, P ((homologyFunctor A n).obj M) :=
  Iff.rfl

instance hasHomologyIn_isClosedUnderIsomorphisms [P.IsClosedUnderIsomorphisms] :
    (hasHomologyIn P).IsClosedUnderIsomorphisms :=
  inferInstanceAs ((homologyFunctor A 0).hasHomologyIn P).IsClosedUnderIsomorphisms

/-- **Complexes with homology in a weak Serre class form a triangulated subcategory** of the
derived category. -/
instance hasHomologyIn_isTriangulated [P.IsWeakSerreClass] :
    (hasHomologyIn P).IsTriangulated :=
  inferInstanceAs ((homologyFunctor A 0).hasHomologyIn P).IsTriangulated

end DerivedCategory
