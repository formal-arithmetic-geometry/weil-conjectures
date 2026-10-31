/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FilteredDerivedOperationStructures

/-! The general filtered derived operation construction.

Source: Stacks Tags 015Q, 015S, 05U2, 05TY; Varshavsky §§5.1.3 and 5.2.2
(blueprint: lem-trf-filtered-derived-operation-lifts).

This intermediate theorem packages the filtered injective-resolution construction,
its graded and forgetful comparisons, and the filtered adjunction construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe wA vA uA wB vB uB
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A common right-derived lift supports every exact-left-adjoint adjunction.
Source: Stacks Tags 015Q, 015S, 05U2, 05TY; Varshavsky §5.2.2.

Proof: for each filtration interval use the exact equivalence
filteredInjectiveComparison from filteredLocalization_injectiveModel and its quasi-inverse.
Apply T to each filtration inclusion; left exactness preserves the inclusions. Every
filtered injective has a finite split filtration, so its image's grades are T of its
grades. Compose the termwise homotopy functor with the quasi-inverse and localization.
The additive homotopy functor and the inverse equivalence preserve shifts and triangles.
The total and graded evaluations of a filtered injective are bounded-below complexes
of ordinary injectives; their images therefore compute the specified ordinary right
derived functor. Uniqueness of derived functors supplies natural comparison isomorphisms.
For L left adjoint to T, exactness of L implies T preserves injectives. Compute Hom
into a filtered-injective resolution, transpose degreewise by the ordinary adjunction,
and use the filtered localization Hom bijection on both sides. Transposition preserves
all filtration conditions and chain homotopies. These natural Hom bijections give the
filtered adjunction. Taking identities gives the usual resolution unit and counit, so
the forgetful equations hold. Apply filteredFunctorGradedComparison to the interval
preserving unit and counit to obtain their graded equations. All intervals, including
none and degenerate intervals with only zero objects, use the same construction.
(blueprint: lem-trf-filtered-derived-adjunction-construction). -/
theorem filteredDerivedAdjunctionConstruction
    {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B]
    [HasDerivedCategory.{wB} B]
    (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T] :
    ∃ lift : FilteredDerivedOperationLift T.rightDerivedFunctorPlus,
      (∀ (L : B ⥤ A) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
        (adj : L ⊣ T), ∃ termwiseLeft : FilteredTermwiseLift L,
        Nonempty (FilteredDerivedAdjunction adj.derivedPlus
          termwiseLeft.toFilteredDerivedOperationLift lift)) := by
  sorry

end CategoryTheory
