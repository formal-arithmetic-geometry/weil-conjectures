/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q96
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.AlgebraicGeometry.PreorderBarTotal
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import Sheaf.CategoryTheory.SequentialTelescopeMono
import Sheaf.AlgebraicGeometry.PreorderBarFilteredAugmentation
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# Transfinite extensions in cocomplete preaisles

Source: Weil conjectures blueprint, `sec-deligne-laumon-a1/sk-p-dl-a1-perverse`,
`lem-per-artin-gabber-affine-curve`, proof Step 2, middle t-structure existence input.
This is the agent-formulated auxiliary lemma for the set-generated-aisle construction;
the blueprint supplies its motivation, not its proof.
(blueprint: lem-per-preaisle-transfinite-monomorphism-closure).
-/

@[expose] public section

set_option autoImplicit false

universe t v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A strictly full preaisle closed under small coproducts contains continuous transfinite
extensions of unbounded complexes whose successive quotients belong to it.
Source: Weil conjectures blueprint, `lem-per-artin-gabber-affine-curve`, proof Step 2,
middle t-structure existence input; agent-formulated auxiliary lemma.
(blueprint: lem-per-preaisle-transfinite-monomorphism-closure).

The well-ordered small type `J`, with least and greatest elements, represents the ordinal
interval `[0, θ]`. The continuity assumption is on each evaluation functor, so it states
exactly that the given transition cocone is a colimit degree by degree at every nonzero
limit. The categorical cokernel is the degreewise quotient complex. No boundedness,
compactness, negative-shift closure, or retract closure is assumed.

Proof plan:
1. Induct along `J`. At its bottom, the complex is zero. At a successor, degreewise
monicity gives a short exact sequence with third term the stated cokernel complex.
Use [lem-weil-pbc-complex-ses-triangle] and extension closure for its derived triangle.
2. At a nonzero limit, the preceding indices form a nonempty small filtered preorder.
Its colimits are exact by [def-sp-grothendieck-abelian]. Form the unbounded bar total
[def-sc-preorder-bar-total]. Its column of simplicial degree p is a coproduct of earlier
complexes, hence its derived image belongs to U by induction and
[lem-kun-grothendieck-derived-coproducts]. Continuity identifies the degreewise colimit
with the limit-stage complex, and [lem-sc-preorder-bar-filtered-augmentation] makes the
bar augmentation to that complex a quasi-isomorphism.
3. Retain bar columns 0 through n to form finite skeleta T_n. The horizontal differential
lowers the column degree, so these are subcomplexes. Their successive quotients are
B_{n+1}[n+1], including the vertical sign (-1)^(n+1). Repeated positive-shift closure
and the short-exact-sequence triangle put each Q(T_n) in U.
4. Let W be the coproduct of all T_n. The map identity minus successor inclusion on W
has cokernel the full bar total B: compatible maps out of the finite partial sums are
exactly maps out of B, degree by degree. The map is monic by
[lem-kun-sequential-telescope-mono]; Grothendieck exact filtered colimits give its
finite-limit preservation hypothesis. This yields a degreewise short exact sequence
0 → W → W → B → 0, using [def-weil-pbc-category-colimit].
5. Derived coproducts put Q(W) in U. Rotate the short-exact-sequence triangle once,
using [def-weil-triangulated-category], to place Q(B) between Q(W) and Q(W)[1].
Extension closure and positive-shift closure now put Q(B) in U.
6. The bar augmentation is inverted by [def-weil-abstract-derived-category]. Closure
under isomorphisms transfers membership to the limit-stage complex. This completes
the induction and gives membership at the greatest element. -/
theorem preaisle_transfinite_monomorphism_closure
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{t} A]
    (U : ObjectProperty (DerivedCategory A)) [U.IsClosedUnderIsomorphisms]
    [U.ContainsZero] [U.IsTriangulatedClosed₂]
    (hcoproducts : ∀ I : Type v, U.IsClosedUnderColimitsOfShape (Discrete I))
    (hshift : ∀ K : DerivedCategory A, U K → U (K⟦(1 : ℤ)⟧))
    {J : Type v} [LinearOrder J] [OrderBot J] [OrderTop J]
    [SuccOrder J] [WellFoundedLT J]
    (E : J ⥤ CochainComplex A ℤ)
    [hcontinuous : ∀ n : ℤ,
      (E ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) n).IsWellOrderContinuous]
    (hzero : IsZero (E.obj ⊥))
    (hmono : ∀ (i j : J) (hij : i ≤ j) (n : ℤ),
      Mono ((E.map (homOfLE hij)).f n))
    (hquotients : ∀ i : J, i < ⊤ →
      U (Q.obj (cokernel (E.map (homOfLE (Order.le_succ i)))))) :
    U (Q.obj (E.obj ⊤)) :=
  sorry

end DerivedCategory
