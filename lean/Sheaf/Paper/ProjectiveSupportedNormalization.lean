module

public import Sheaf.Paper.DiagonalCoefficientCategory
public import Sheaf.Paper.RationalP1SecondPullComparison

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar

/--
The inverse support isomorphism is the normalized lower-star composite,
congruence, and identity comparison on the regular module.
Source: the first step of the second identity proof in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-triangle.proof.md`.
The proof applies the underlying sheaf normalization and faithfulness of
module morphisms.
(blueprint: lem-sfb-projective-supported-source-arrow-derived-core)
-/
theorem projective_supported_normalization (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L) :
    d.support₂.iso.inv =
      (CondensedRing.lowerStarComp Λ (diagonalImmersion Y) (secondProjection Y) ≪≫
        CondensedRing.lowerStarCongr Λ d.support₂.over_eq ≪≫
          CondensedRing.lowerStarId Λ (ProjectiveLine Y)).hom.app
            (Mod.regular (condensedRingObj Λ (ProjectiveLine Y))) := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
