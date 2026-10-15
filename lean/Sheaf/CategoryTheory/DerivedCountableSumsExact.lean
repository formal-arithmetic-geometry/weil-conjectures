/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-!
# Exact countable sums compute derived coproducts

Source: Stacks Project, Derived Categories, Tag 0A5L, Lemma `lemma-direct-sums`,
statement and proof (blueprint: lem-kun-derived-countable-sums-exact).
-/

@[expose] public section

universe w v u t

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- In an abelian category with exact countable coproducts, the termwise coproduct
of unbounded cochain complexes, with the images of its specified coprojections, is
also a coproduct in the derived category. The index type may be empty and may lie
in any universe. The termwise complex and its differential are the actual
construction `HomologicalComplex.coconeOfHasColimitEval`.

Source: Stacks Project, Derived Categories, Tag 0A5L, Lemma `lemma-direct-sums`
(blueprint: lem-kun-derived-countable-sums-exact).

Proof plan:
1. Form sums degreewise. The universal property induces the differential, whose
square is zero by checking every coprojection. Chain maps and homotopies out of
this complex assemble degreewise, so it is a coproduct in the homotopy category.
2. Sum the short exact sequences for cycles, boundaries and cohomology. Exactness
identifies the cohomology of the sum with the sum of the cohomologies, naturally
in chain maps. Thus countable sums of quasi-isomorphisms are quasi-isomorphisms;
quasi-isomorphisms also satisfy two-out-of-three.
3. By `lem-pc-quasi-isomorphisms-multiplicative-system` and
`lem-pc-right-fraction-representation`, represent each derived map by a roof.
Sum the denominators and assemble the numerators. Step 2 inverts the summed
denominator, giving a map with the desired restrictions. Every derived target
is represented by a complex.
4. By `lem-pc-right-fraction-common-refinement`, equality of localized maps from
the homotopy category can be witnessed after precomposition by a quasi-isomorphism:
apply common refinement to roofs with identity denominators.
5. For uniqueness, put two roofs out of the sum over a common denominator using
the right-calculus square axiom; two-out-of-three makes both refinements valid.
6. Apply the square axiom to each coprojection and the common denominator. Equal
restrictions and step 4 give componentwise refinements on which the numerators
agree and whose maps to the original summands are quasi-isomorphisms.
7. Sum these refinements, including the homotopies witnessing their equations.
The summed map to the original sum is a quasi-isomorphism by step 2. Hence its
factor to the common denominator is one by two-out-of-three. Cancel its image
to obtain equality of the localized numerators and therefore of the two maps.
8. These existence and uniqueness assertions are the coproduct universal property.
For an empty family the termwise sums are zero objects. The empty summed
denominators are maps between zero complexes, hence isomorphisms; the same
argument includes the empty coproduct, without any boundedness assumption. -/
theorem isColimit_mapCocone_countableSum
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{t} A]
    [HasCountableCoproducts A] [CountableAB4 A]
    (I : Type w) [Countable I] (K : I → CochainComplex A ℤ) :
    Nonempty (IsColimit ((Q (C := A)).mapCocone
      (HomologicalComplex.coconeOfHasColimitEval (Discrete.functor K)))) := by
  sorry

end DerivedCategory
