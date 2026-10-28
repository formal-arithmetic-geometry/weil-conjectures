/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.Paper.RationalP1ScalarChernMaps
public import Sheaf.Paper.DerivedCalculationInstances
public import Sheaf.Paper.AmbientTwistedUnitMate
public import Sheaf.Paper.ScalarTraceEquation
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
/-- Assemble the twisted-unit component from the explicit trace witness by
ambient mate naturality and the shifted line square.
(blueprint: lem-sfb-scalar-component-from-trace) -/
theorem scalar_component_from_trace
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (htrace : ScalarTraceWitness l c k p hpl Y) :
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
        (scalarQLineIso l c k p hpl Y).hom ≫ u₂  := by sorry
end AlgebraicGeometry.ProEtale.RationalP1
