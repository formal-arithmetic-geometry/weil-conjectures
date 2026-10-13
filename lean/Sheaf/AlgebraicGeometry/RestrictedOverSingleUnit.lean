/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.RestrictedOverSingleData

/-! # Unit law for restricted fixed-coefficient single complexes

Source: Stacks Project, Tags 09Z1 and 0EZM, restriction of fixed coefficients.
(blueprint: lem-sbc-restricted-over-single-unit).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Unit law for a fixed-coefficient restricted single complex at one diagram object.
Source: Stacks Project, Tags 09Z1 and 0EZM, canonical fixed-coefficient comparisons.
(blueprint: lem-sbc-restricted-over-single-unit).

Proof: Substitute D₀.map_id. The induced pullback map is identity by its two projection
identities. Expand restrictedOverSingleIso.hom and rawAffineRestrictedCoefficient.
The two inverse-image composition unit laws reduce the three sheaf comparisons to
upperStarId. The natural comparison of singleFunctor with inverse image respects
this unit: in degree zero it is the identity comparison; every other degree is zero.
Consequently its hom is the displayed mapHomologicalComplex unit, transported along
the restricted diagram map_id equality. Proof irrelevance makes the choice of equality proof
immaterial. This argument also applies to the zero sheaf, the empty scheme and identity
structure maps. -/
theorem restrictedOverSingle_unit {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
    {I : Type u} [Category.{u} I] (D₀ : I ⥤ Over W) (U : S.Etale) (i : I) :
    (restrictedOverSingleIso k F (D₀.map (𝟙 i)) U).hom =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1})
          ((restrictedOverDiagram k D₀ U).map_id i)))
        (ComplexShape.up ℤ)).hom.app (restrictedOverSingle k F (D₀.obj i) U) ≫
      (NatIso.mapHomologicalComplex
        (upperStarId AddCommGrpCat.{u + 1} ((restrictedOverDiagram k D₀ U).obj i))
        (ComplexShape.up ℤ)).hom.app (restrictedOverSingle k F (D₀.obj i) U) := by sorry

end AlgebraicGeometry.Etale
