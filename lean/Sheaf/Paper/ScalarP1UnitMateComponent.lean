/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RationalP1ScalarChernMaps

/-! The unit component of the scalar exchange mate.

Source: the adjunction mate and root-normalized line comparison in the second
rational P1 triangle.
(blueprint: lem-sfb-rational-p1-scalar-chern-base-change-unit-component-core)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line diagram trace singleUnitIso
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange

/-- The scalar exchange carries the twisted unit to the twisted unit.

This is the categorical unit component, with the completed Chern data removed;
the latter is unused by the component equation. The proof expands the exchange
mate and uses the root-normalized line comparison.
(blueprint: lem-sfb-rational-p1-scalar-chern-base-change-unit-component-core) -/
theorem scalar_p1_unit_mate_component
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))] :
    let Λ := (coefficient l c).X
    let L := line l c
    let T := fun X : Scheme.{u} ↦
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj (L X)) ⟦(2 : ℤ)⟧
    let uq := scalarTwistedUnit Λ (ProjectiveLine Y ↘ Y) (T Y) (T (ProjectiveLine Y))
      (scalarQLineIso l c k p hpl Y)
    let u₂ := scalarTwistedUnit Λ (secondProjection Y)
      (T (ProjectiveLine Y)) (T (diagonalSurface Y)) (secondLineComparison l c k p hpl Y)
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    F.map uq ≫ secondTraceExchange l c k p hpl Y =
        (scalarQLineIso l c k p hpl Y).hom ≫ u₂ := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
