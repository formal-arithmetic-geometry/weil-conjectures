/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Successive lower truncation triangle

Source: literature/stacks-project/perfect.tex, Tag 08D4 proof of part (2)
(blueprint: lem-pc-derived-lower-truncation-step-triangle).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- The canonical transition between successive lower truncations lies in a
triangle with the shifted cohomology object.
Source: Stacks Project, Tag 08D4, proof of part (2)
(blueprint: lem-pc-derived-lower-truncation-step-triangle).

Choose a complex representative K. The canonical lower truncations represent
these derived truncations: the quotient representatives are quasi-isomorphic to
K.truncGE, compatibly with transitions (Tag 08J5).
Apply lem-pc-derived-lower-truncation-step-ses at m = -n to obtain the short
exact sequence with kernel C_m(K) and its quasi-isomorphism from H^m(K)[-m].
Apply lem-weil-pbc-complex-ses-triangle to obtain the distinguished triangle
whose middle arrow is the quotient transition. The quasi-isomorphism becomes
an isomorphism in the derived category (def-weil-abstract-derived-category).
Transport the triangle along this isomorphism using TR1
(def-weil-triangulated-category). The naturality of the SES and its triangle
identifies the transition with the canonical truncation-tower arrow. -/
theorem exists_lowerTruncationStepTriangle
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (E : DerivedCategory C) (n : ℤ) :
    ∃ (f : (Q.obj ((CochainComplex.singleFunctor C 0).obj
          ((homologyFunctor C (-n)).obj E)))⟦n⟧ ⟶
        ((TStructure.t (C := C)).truncGE (-n)).obj E)
      (h : ((TStructure.t (C := C)).truncGE (-n + 1)).obj E ⟶
        ((Q.obj ((CochainComplex.singleFunctor C 0).obj
          ((homologyFunctor C (-n)).obj E)))⟦n⟧)⟦(1 : ℤ)⟧),
      Triangle.mk f
        (((TStructure.t (C := C)).natTransTruncGEOfLE (-n) (-n + 1) (by omega)).app E) h
          ∈ distTriang (DerivedCategory C) := by
  sorry

end DerivedCategory
