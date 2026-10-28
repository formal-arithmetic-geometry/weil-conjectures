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

/-- Post-normalization comparison for the supported source.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-triangle.proof.md,
Second identity, the derived trace comparison after removing the ordinary support isomorphism.
(blueprint: lem-sfb-projective-supported-source-arrow-derived-core)

This is the residual compatibility between the canonical derived unit and the
conjugate section comparison. It is strictly smaller than the final statement
because it omits the support normalization isomorphism.
-/
theorem supported_source_arrow_derived_core
    (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L) :
    diagonalTraceRightSingle
          (CondensedRing.lowerStar Λ (secondProjection Y)) d.R₂
          (source Λ Y) ≫
        (secondDiagramPushIso Λ Y L d).hom.app
          ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
            (source Λ Y)) =
      (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map d.support₂.iso.inv ≫
        (pushSectionIso Λ Y).hom.app (unit Λ (ProjectiveLine Y)) ≫
        (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
          (supportedUnitIso Λ Y).hom := by
  sorry

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
  rw [supported_source_arrow_derived_core Λ Y L d]
  rw [← Category.assoc]
  rw [← (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map_comp]
  rw [Iso.hom_inv_id]
  simp

end AlgebraicGeometry.ProEtale.RationalP1
