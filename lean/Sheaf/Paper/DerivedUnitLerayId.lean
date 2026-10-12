/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-! # Coherence of the derived unit and Leray comparison -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
/-- The derived unit followed by Leray and the derived inverse-image identity is
identity. Source: Stacks Project, Tags 015M and 03CB.
(blueprint: lem-weil-pbc-derived-unit-leray-id).

Proof: Write U for D((id_X)^*), R for R((id_X)_*), G for RGamma_X, and E:U≅id for
mapDerivedCategoryNatIso(upperStarId) followed by mapDerivedCategoryIdIso. The conjugate
identity isomorphism of R is obtained by right deriving lowerStarId. The unit equation is
eta_id,K followed by R(E_K) equal to the inverse direct-image identity comparison at K. This
follows by the underived unit equation, the derived adjunction unit characterization, and
uniqueness of transformations of right derived functors extending it.

The underived identification (id_X)_* followed by Gamma_X ≅ Gamma_X evaluates sheaves at the
terminal object and hence equals Gamma_X applied to lowerStarId. Consequently the Leray
comparison for id_X is G applied to the derived direct-image identity comparison: both
comparisons satisfy the same equation with the derived global-sections unit. Uniqueness of right
derived comparisons identifies them.

Naturality of the Leray comparison at E_K rewrites G(eta_id,K); lambda_id,U(K); G(E_K) as
G(eta_id,K); G(R(E_K)); lambda_id,K. Substitute the unit equation from step 1 and the
identification from step 2. The inverse and forward direct-image identity comparisons cancel,
and G preserves identity. The equation holds for every derived object, since all transformations
in this argument are on the unbounded derived category computed using K-injectives; no
boundedness of K is used. -/
theorem derivedUnitLeray_id (X : Scheme.{u})
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
      ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (𝟙 X)).unit.app K) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso AddCommGrpCat.{u + 1} (𝟙 X)).hom.app
      ((upperStar AddCommGrpCat.{u + 1} (𝟙 X)).mapDerivedCategory.obj K) ≫
    (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
      ((Functor.mapDerivedCategoryNatIso (upperStarId AddCommGrpCat.{u + 1} X) ≪≫
        Functor.mapDerivedCategoryIdIso
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})).hom.app K) = 𝟙 _ := by
  sorry

end AlgebraicGeometry.Etale
