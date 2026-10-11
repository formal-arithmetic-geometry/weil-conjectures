/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Exact.Basic

/-!
# Exactness of homotopy morphisms into a termwise injective complex

Source: Stacks Project, injectives.tex, Lemma lemma-characterize-K-injective,
successor step (blueprint: lem-pur-kinjective-homotopy-exact-injective-target).
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CochainComplex

/-- Source: Stacks Project, injectives.tex, Lemma lemma-characterize-K-injective,
successor step (blueprint: lem-pur-kinjective-homotopy-exact-injective-target).
For a short exact sequence of cochain complexes, precomposition on homotopy classes
into a termwise injective target is exact at the middle group.

Proof: In each degree, injectivity of the target terms (def-sp-injective-resolutions),
the cokernel property, and epimorphy give a short exact sequence of Hom groups.
Products give a short exact sequence of Hom complexes, since precomposition commutes
with their differentials. Apply the long exact cohomology sequence
(lem-weil-pbc-complex-ses-homology-long-exact) at degree zero. Degree-zero cocycles are
chain maps and coboundaries are null-homotopic maps, so degree-zero Hom cohomology is
Hom in the homotopy category (def-weil-abstract-derived-category). This identification
commutes with precomposition, giving the claimed exactness. -/
theorem homotopy_hom_exact_of_injective {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (I : CochainComplex C ℤ) (hI : ∀ n : ℤ, Injective (I.X n)) :
    Function.Exact
      (Preadditive.leftComp ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map S.g))
      (Preadditive.leftComp ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map S.f)) := by
  sorry

end CochainComplex
