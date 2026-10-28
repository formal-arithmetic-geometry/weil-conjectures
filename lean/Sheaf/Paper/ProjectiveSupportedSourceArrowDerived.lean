module

public import Sheaf.Paper.ProjectiveDiagonalComposition
public import Sheaf.Paper.RationalP1SecondPullComparison
public import Sheaf.Paper.DiagonalCoefficientCategory

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Derived-unit evaluation of the supported source.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-triangle.proof.md,
Second identity, evaluation of the canonical right-derived unit before cancellation.
(blueprint: lem-sfb-projective-supported-source-arrow-derived)
-/
theorem supported_source_arrow_derived
    (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L) :
    (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map d.support₂.iso.hom ≫
        diagonalTraceRightSingle
          (CondensedRing.lowerStar Λ (secondProjection Y)) d.R₂
          (source Λ Y) ≫
        (secondDiagramPushIso Λ Y L d).hom.app
          ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
            (source Λ Y)) =
      (pushSectionIso Λ Y).hom.app (unit Λ (ProjectiveLine Y)) ≫
        (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
          (supportedUnitIso Λ Y).hom := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
