/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredLocalization
import Sheaf.CategoryTheory.DoubleComplexTotal
import Sheaf.Algebra.Homology.FirstQuadrantAugmentation
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.Algebra.Homology.FilteredConeLocalization
import Sheaf.CategoryTheory.EnoughStrictFilteredInjectives
import Sheaf.Paper.FiniteFilteredGradedExactness
import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Filtered injectives compute bounded-below filtered localization

Source: Stacks Project, Derived Categories, Tags 05TW
(`lemma-right-resolution-by-filtered-injectives`), 05TY
(`lemma-morphisms-into-filtered-injective-complex`) and 015Q
(`lemma-filtered-localization-functor`)
(blueprint: lem-trf-filtered-localization-injective-model).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{w} C]

/-- Filtered-injective resolutions, the localization Hom bijection, and the exact
comparison equivalence, compatibly with forgetting and every graded-piece functor.
`B = none` imposes no common filtration interval on the terms of a complex;
`B = some (a,b)` gives all assertions with `Fᵃ = ⊤`, `Fᵇ⁺¹ = ⊥` throughout.
`p = none` denotes forgetting and `p = some n` denotes the `n`-th graded piece.

Source: Stacks, Derived Categories, Tags 05TW, 05TY and 015Q.
Proof (the twelve steps of the DAG node):
1. Use `def-sp-filtration` and `def-sp-filtered-complex-subquotients` for subobject
   and quotient filtrations. Graded exactness gives strict exactness by
   `lem-trf-finite-filtered-graded-exactness`; use the cone triangulation of
   `lem-trf-filtered-cone-localization`. Shift the lower cochain bound to zero.
2. Repeatedly embed each successive quotient strictly into a filtered injective,
   using `lem-trf-enough-strict-filtered-injectives`. The quotient-inclusion
   composites define a resolution of a single object (05TT).
3. Lift a map between single-object resolutions one cochain degree at a time.
   The extension property of filtered injectives extends across strict image
   inclusions; graded exactness identifies the required coimages (05TU).
4. For a strict short exact sequence, extend the augmentation and construct the
   off-diagonal maps in a horseshoe resolution. Its terms are the two outside
   terms' direct sums. The equation on off-diagonal maps makes the differential
   square zero. The homology long exact sequence and its naturality
   (`lem-weil-pbc-complex-ses-homology-long-exact` and
   `lem-weil-pbc-complex-ses-long-exact-naturality`) prove the middle augmentation
   is a graded quasi-isomorphism (05TV).
5. Resolve the kernels and coimages of the original differentials. Lift the maps
   from coimages to the next kernels and insert them between the horseshoe
   projections and inclusions. Their successive composites vanish. This gives
   the first-quadrant double complex of `def-sp-double-complex-total` (05TW).
6. Totalize with the standard signs. Every diagonal is finite, so its terms are
   filtered injective. Grading commutes with these finite sums. Apply
   `lem-sc-first-quadrant-column-augmentation` to the flipped double complex;
   multiplication by `(-1)^(i*r)` identifies the two total sign conventions and
   is the identity on the augmentation. Shift back to obtain the resolution.
7. A map from a graded-acyclic complex into a bounded-below filtered-injective
   complex is null-homotopic. Inductively factor its residual through the strict
   image of the source differential and extend using filtered injectivity
   (`lem-trf-finite-filtered-graded-exactness`,
   `lem-trf-enough-strict-filtered-injectives`; 05TX).
8. Apply step 7 to the cone and shifted cone of a graded quasi-isomorphism.
   The cone formulas give bijectivity of precomposition on Hom into an injective
   complex (`lem-trf-filtered-cone-localization`; 05TY(1)).
9. Descend the contravariant Hom functor through localization. Evaluation of its
   action on a localized arrow at the identity gives the inverse of the
   localization Hom map; naturality proves both inverse equations (05TY(2)).
10. The comparison is fully faithful by step 9 and essentially surjective by
   step 6. Inclusion and localization preserve cone triangles and shifts, so
   this is an exact equivalence (`lem-trf-filtered-cone-localization`; 015Q).
11. Split the successive filtration sequences of a filtered injective, starting
   at the final nonzero step. Its underlying object is a finite sum of injective
   graded objects and therefore injective. Grading inverts filtered
   quasi-isomorphisms by definition; forgetting does so by graded exactness.
   The termwise squares descend canonically through localization (015Q).
12. Every embedding, quotient, kernel, finite sum and extension above retains a
   prescribed filtration interval. Thus the same assertions and comparison
   squares hold for each fixed interval, including a single graded piece and
   the zero object (05TS, 05TW, 05TX, 05TY and 015Q).
(blueprint: lem-trf-filtered-localization-injective-model). -/
theorem filteredLocalization_injectiveModel (B : Option (ℤ × ℤ)) :
    (∀ K : CochainComplex.Plus (FiniteFilteredObjects C B false),
      ∃ (I : CochainComplex.Plus (FiniteFilteredObjects C B true))
        (f : K ⟶ (filteredInjectiveInclusion C B).mapCochainComplexPlus.obj I),
        finiteFilteredQuasiIso C B
          ((HomotopyCategory.Plus.quotient (FiniteFilteredObjects C B false)).map f)) ∧
    (∀ K I : FiniteFilteredHomotopyPlus C B false,
      (∀ n p : ℤ, Injective ((I.obj.as.X n).obj.filtration.gradedPiece p)) →
      Function.Bijective
        ((finiteFilteredQh C B).map : (K ⟶ I) →
          ((finiteFilteredQh C B).obj K ⟶ (finiteFilteredQh C B).obj I))) ∧
    (filteredInjectiveComparison C B).IsEquivalence ∧
    (filteredInjectiveComparison C B).IsTriangulated ∧
    (∀ (I : FiniteFilteredHomotopyPlus C B true) (n : ℤ) (p : Option ℤ),
      Injective ((filteredEvaluation C B true p).obj (I.obj.as.X n))) ∧
    (∀ p : Option ℤ, Nonempty
      (filteredInjectiveComparison C B ⋙ finiteFilteredDerivedEvaluation C B p ≅
        (filteredEvaluation C B true p).mapHomotopyCategoryPlus ⋙
          DerivedCategory.Plus.Qh)) := by
  sorry

end CategoryTheory
