module
public import Sheaf.Paper.ProjectiveDiagonalComposition
public import Sheaf.CategoryTheory.RightDerivedSingleH0
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar
public abbrev derivedAdj {X S : Scheme.{u}} (f : X ⟶ S) :=
  CondensedRing.derivedUpperStarLowerStarAdjunction Λ f
public def ordinarySection (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) :
    CondensedRing.upperStar Λ f ⋙ CondensedRing.upperStar Λ (diagonalImmersion Y) ≅ 𝟭 _ :=
  (CondensedRing.upperStarComp Λ (diagonalImmersion Y) f).symm ≪≫
    CondensedRing.upperStarCongr Λ h ≪≫
      CondensedRing.upperStarId Λ (ProjectiveLine Y)
public def derivedSection (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) :
    (CondensedRing.upperStar Λ f).leftDerivedFunctor ⋙
      (CondensedRing.upperStar Λ (diagonalImmersion Y)).leftDerivedFunctor ≅
      𝟭 (DerivedCategory (Modules Λ (ProjectiveLine Y))) := by
  have e := pullSectionIso Λ Y f h
  dsimp only [moduleObjectDerivedPullback] at e
  exact e
/-- Single-complex derived section compatibility.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-triangle.proof.md.
(blueprint: lem-sfb-projective-supported-source-arrow-derived-core)
-/
theorem projective_section_single (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y))
    (M : Modules Λ (ProjectiveLine Y)) :
    (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map
          ((conjugateIsoEquiv Adjunction.id
            ((CondensedRing.upperStarLowerStarAdjunction Λ f).comp
              (CondensedRing.upperStarLowerStarAdjunction Λ (diagonalImmersion Y)))
            (ordinarySection Λ Y f h)).hom.app M) ≫
        (CondensedRing.lowerStar Λ f).singleRightDerivedUnit.app
          ((CondensedRing.lowerStar Λ (diagonalImmersion Y)).obj M) ≫
      (CondensedRing.lowerStar Λ f).rightDerivedFunctor.map
        ((CondensedRing.lowerStar Λ (diagonalImmersion Y)).singleRightDerivedUnit.app M) =
      (conjugateIsoEquiv Adjunction.id
        ((derivedAdj Λ f).comp (derivedAdj Λ (diagonalImmersion Y)))
        (derivedSection Λ Y f h)).hom.app
        ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj M) := by
  sorry
end AlgebraicGeometry.ProEtale.RationalP1
