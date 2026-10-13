/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # The exact derived adjunction counit on a single complex

Source: Stacks Project, Tag 0AX3, derived trace as an adjunction counit.
(blueprint: lem-sc-exact-derived-adjunction-single-counit).
-/

@[expose] public section

universe uA uB vA vB wA wB

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Adjunction

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasKInjectiveResolutions A] [HasKInjectiveResolutions B]

/-- The single comparison for an exact right adjoint preserves the derived counit.
Source: Stacks Project, Tag 0AX3, trace-map counit comparison
(blueprint: lem-sc-exact-derived-adjunction-single-counit).

Proof: Apply the factorization formula for the counit of the localized adjunction
at the homotopy image of L[0]. Replace the exact right-derived unit by the inverse
localization comparison, using its uniqueness factorization. The counit of the
homotopy adjunction is the quotient of the termwise counit. The single comparisons
identify this termwise counit with the single of the underived counit, by naturality
in the sole nonzero degree. Cancel the invertible exact-functor comparisons to obtain
the displayed equality. No faithfulness, nonzero object or boundedness is needed. -/
theorem exact_derivedAdjunction_single_counit {T : A ⥤ B} {H : B ⥤ A}
    [T.Additive] [H.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adj : T ⊣ H) (L : B) :
    T.mapDerivedCategory.map (H.singleFunctorCompRightDerivedFunctorIso.inv.app L) ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app
        ((DerivedCategory.singleFunctor B 0).obj L) =
    (T.mapDerivedCategorySingleFunctor 0).hom.app (H.obj L) ≫
      (DerivedCategory.singleFunctor B 0).map (adj.counit.app L) := by
  sorry

end CategoryTheory.Adjunction
