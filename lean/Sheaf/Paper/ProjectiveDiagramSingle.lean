module
public import Sheaf.Paper.RationalP1SecondPullComparison
public import Sheaf.CategoryTheory.RightDerivedSingleH0
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
/- Diagram-unit comparison for the single complex. Source: second identity proof.
(blueprint: lem-sfb-projective-supported-source-arrow-derived-core) -/
theorem projective_diagram_single (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L) :
    diagonalTraceRightSingle (CondensedRing.lowerStar Λ (secondProjection Y)) d.R₂
        (source Λ Y) ≫
      (secondDiagramPushIso Λ Y L d).hom.app
        ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
          (source Λ Y)) =
      (CondensedRing.lowerStar Λ (secondProjection Y)).singleRightDerivedUnit.app
        (source Λ Y) := by sorry
end AlgebraicGeometry.ProEtale.RationalP1
