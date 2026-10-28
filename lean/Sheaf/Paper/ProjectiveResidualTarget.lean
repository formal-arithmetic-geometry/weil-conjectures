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
/- Residual section and support comparison after the diagram unit is identified.
Source: second identity proof.
(blueprint: lem-sfb-projective-supported-source-arrow-derived-core) -/
theorem projective_residual_target (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L) :
    (CondensedRing.lowerStar Λ (secondProjection Y)).singleRightDerivedUnit.app
        (source Λ Y) =
      (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map
          d.support₂.iso.inv ≫
        (pushSectionIso Λ Y).hom.app (unit Λ (ProjectiveLine Y)) ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
        (supportedUnitIso Λ Y).hom := by sorry
end AlgebraicGeometry.ProEtale.RationalP1
