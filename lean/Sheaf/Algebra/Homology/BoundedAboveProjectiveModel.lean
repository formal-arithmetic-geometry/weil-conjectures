/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Bounded-above projective models of derived module objects

Source: Stacks Project, Tags 0645 and 0646, and the downward construction of Tag 05T7
(blueprint: lem-weil-pbc-bounded-above-projective-model).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- An object with no cohomology above `b` has a projective complex model zero above `b`.
Source: Stacks Project, Tags 0645 and 0646, parts (2) and (3)
(blueprint: lem-weil-pbc-bounded-above-projective-model).

Proof:
1. Choose a complex K representing C using the localization Q. Its cohomology vanishes
   above b since cohomology factors through Q.
2. Set L, its differentials, and a map f : L → K to zero above b. Descend from b.
   At degree n form the submodule T of K^n ⊕ L^{n+1} of pairs (x,y) satisfying
   d_K x = f y and d_L y = 0 (the fibre-product construction of Tag 05T7).
3. Take L^n to be the free module on the underlying set of T. Its canonical surjection
   onto T, followed by the two projections, defines f^n and d_L^n. The equations for T
   make f a complex map and give d_L squared equal to zero, extending the constructed tail.
4. Each cycle x in K^n lifts via (x,0) in T to a cycle in L^n. Thus H^n(f) is surjective.
5. If a cycle y in L^n maps to the boundary d_K x, lift (x,y) in degree n-1.
   Its lift has differential y, so H^n(f) is injective. Above b both cohomologies vanish.
6. The free terms are projective by Module.Projective.of_free, including the zero terms
   (free on the empty basis). Q inverts the resulting quasi-isomorphism f; compose the
   isomorphism Q(L) ≅ Q(K) with Q(K) ≅ C. The exact upper bound b is unchanged. -/
theorem exists_boundedAbove_projective_model
    (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    (C : DerivedCategory (ModuleCat.{max u v} A)) (b : ℤ)
    (hC : ∀ i : ℤ, b < i → IsZero ((homologyFunctor (ModuleCat.{max u v} A) i).obj C)) :
    ∃ L : CochainComplex (ModuleCat.{max u v} A) ℤ,
      (∀ i : ℤ, Module.Projective A (L.X i)) ∧
      (∀ i : ℤ, b < i → IsZero (L.X i)) ∧ Nonempty (Q.obj L ≅ C) := by
  sorry

end DerivedCategory
