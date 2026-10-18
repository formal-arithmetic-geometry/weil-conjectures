/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# Bounded-above resolutions from a quotient-generating class

Source: Stacks Project, Derived Categories, Tag 05T7,
`derived-lemma-subcategory-left-resolution`, part (1)
(blueprint: lem-sfb-subcategory-left-resolution).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A bounded-above complex admits a termwise epimorphic quasi-isomorphism from a complex
in any quotient-generating class containing a zero object, with the same upper bound.

Source: Stacks Project, Derived Categories, Tag 05T7,
`derived-lemma-subcategory-left-resolution`, part (1)
(blueprint: lem-sfb-subcategory-left-resolution).

Proof (the seven steps of the node):
1. Descend from degree `a + 1`. At stage `n`, prescribe terms in the class in degrees
   at least `n`, zero above `a`, with epic component maps to `K`, an epic map on
   degree-`n` cycles, and cohomology isomorphisms in degrees greater than `n`.
   The chosen zero object in the class supplies the initial stage. Complexes and
   cohomology are those of [def-weil-abstract-derived-category] in [def-sp-abelian].
2. Form `T = K^(n-1) ×_{Z^n K} Z^n P`, using the differential factored through cycles
   and the epic cycle map. Choose an epic cover `Q → T` with `Q` in the class.
   Its projections give the new component and differential. The pullback equation
   gives the chain-map identity, and the cycle inclusion gives the square-zero identity.
3. The new component is epic: lift a generalized element of `K^(n-1)` first along
   the cycle epimorphism and then along `Q → T`, after epimorphic refinements.
   Apply [lem-sp-abelian-refinements](a) and compose the refinements.
4. The new cycle map is epic: a cycle `x` gives the pair `(x, 0)` in `T`. Lift it
   along `Q → T` after an epimorphic refinement. Its zero second component makes
   the lift a cycle. Apply [lem-sp-abelian-refinements](a).
5. The new cohomology map in degree `n` is epic: lift a cohomology class through
   the cycle quotient and then through the epic cycle map, using
   [lem-sp-abelian-refinements](a) twice.
6. It is monic: lift a class in its kernel to a cycle. Its image is a boundary
   after refinement by [lem-sp-abelian-refinements](c). The resulting pair in `T`
   lifts along `Q → T` after another refinement, making the original cycle a boundary.
   Cancel the refinements to get a zero class. Mono and epi imply iso in an abelian
   category, since an epic monomorphism is a cokernel of zero.
7. Recurse on `k : ℕ` with lower endpoint `a + 1 - k`, retaining all assigned data.
   Every integer degree is reached. The cohomology map in degree `j` becomes an
   isomorphism at stage `j - 1` and is unchanged thereafter; above `a` both complexes
   vanish. The resulting chain map is thus a quasi-isomorphism, epic in every degree,
   with all terms in the class and zero terms above `a`.
-/
theorem exists_subcategory_left_resolution
    {C : Type u} [Category.{v} C] [Abelian C]
    (P : C → Prop) (hzero : ∃ Z : C, P Z ∧ IsZero Z)
    (hcover : ∀ X : C, ∃ (Y : C) (p : Y ⟶ X), P Y ∧ Epi p)
    (a : ℤ) (K : CochainComplex C ℤ)
    (hK : ∀ n : ℤ, a < n → IsZero (K.X n)) :
    ∃ (L : CochainComplex C ℤ) (f : L ⟶ K),
      QuasiIso f ∧ (∀ n : ℤ, P (L.X n)) ∧ (∀ n : ℤ, Epi (f.f n)) ∧
        (∀ n : ℤ, a < n → IsZero (L.X n)) := by
  sorry

end CochainComplex
