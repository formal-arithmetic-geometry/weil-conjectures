/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.MonCat.Limits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.MonCat.FilteredColimits

/-!
# Commutative monoid sheafification in a containing universe

Source: Stacks Project, Sites, Tag 00YR, assertions (alpha), (beta), (gamma), (epsilon)
(blueprint: lem-trf-commutative-monoid-sheafification).

The universal properties specify both the monoid sheafification and the underlying
set sheafification with exactly the same unit. The coefficient universe contains
both site universes; no equality with either site universe is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v t

open CategoryTheory

namespace CategoryTheory

/-- Every monoid presheaf has a sheafification, and forgetting its algebraic structure
preserves this sheafification and its unit. Source: Stacks Tag 00YR, assertions
(alpha), (beta), (gamma), (epsilon)
(blueprint: lem-trf-commutative-monoid-sheafification).

Proof: take the underlying set sheafification. Products of its locally represented
sections are defined after passing to a common covering refinement; equality after
further refinement proves independence of representatives. Multiplication and the
unit descend, and the commutative monoid identities hold locally and hence globally.
This makes restrictions and the sheafification unit monoid homomorphisms. A monoid
presheaf map to a monoid sheaf extends uniquely as a set sheaf map; multiplication
and unit preservation may again be checked locally. This gives the monoid universal
property. By construction the underlying map has the set universal property too.
This is also the concrete plus-plus argument behind Mathlib's sheafification
adjunction and its comparison with the forgetful functor.
-/
theorem commutative_monoid_sheafification {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ CommMonCat.{max u v t}) :
    (Presheaf.IsSheaf J P ↔
      Presheaf.IsSheaf J (P ⋙ forget CommMonCat.{max u v t})) ∧
    ∃ (L : Sheaf J CommMonCat.{max u v t}) (η : P ⟶ L.obj),
      (∀ H : Sheaf J CommMonCat.{max u v t},
        Function.Bijective (fun f : L ⟶ H ↦ η ≫ f.hom)) ∧
      Presheaf.IsSheaf J (L.obj ⋙ forget CommMonCat.{max u v t}) ∧
      (∀ H : Sheaf J (Type (max u v t)),
        Function.Bijective (fun f : L.obj ⋙ forget CommMonCat.{max u v t} ⟶ H.obj ↦
          Functor.whiskerRight η (forget CommMonCat.{max u v t}) ≫ f)) := by
  sorry

end CategoryTheory
