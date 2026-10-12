/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.RingTheory.Flat.CategoryTheory
import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatTelescopeClosure

/-!
# Bounded-above flat module complexes are K-flat

Source: Stacks Project, More on Algebra, Lemma 15.59.1 (Tag 064K)
(blueprint: lem-pc-module-bounded-flat-kflat).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- (blueprint: lem-pc-module-bounded-flat-kflat) Stacks Project, More on Algebra,
Lemma 15.59.1 (Tag 064K): a bounded-above cochain complex of flat modules over a
commutative ring is K-flat. Concretely, tensoring it with every acyclic complex
and taking the total complex gives an acyclic complex.

Proof: The first clause of `lem-pc-kflat-closure` applies to the one-point ringed
site with ring `R`. On that site sheaves of modules, their tensor products, and
acyclic complexes identify with modules and their corresponding constructions.
The definition `def-pc-kflat-complex` then gives the asserted acyclicity. -/
theorem acyclic_mapBifunctor_of_boundedAbove_flat
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hflat : ∀ i : ℤ, Module.Flat R (P.X i)) :
    ∀ L : CochainComplex (ModuleCat.{u} R) ℤ, L.Acyclic →
      (mapBifunctor L P (MonoidalCategory.curriedTensor _)).Acyclic := by
  sorry

end CochainComplex
