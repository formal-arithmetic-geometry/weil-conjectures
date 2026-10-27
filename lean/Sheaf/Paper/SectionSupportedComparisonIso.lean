/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H7
-/
module

public import Sheaf.Paper.SectionCompactSourceMaps
import all Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization

/-! # Invertibility of a supported-constant comparison component

Source: blueprint rank-one Thom proof, Step 3; Stacks Tags 095L and 0F7F.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SectionCompactSource
variable (A : Type (u + 1)) [CommRing A]

attribute [local instance 2000] Abelian.toPreadditive
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] Compactification.copy Compactification.ofIsProper
  Etale.derivedPlusFormalism CompactSupportFormalism.shriek
  ProEtale.coherenceEtaleFunctor Etale.rightDerivedLowerStarPlus
attribute [local irreducible] Functor.rightDerivedFunctorPlus Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
attribute [local implicit_reducible] TwoSquare MorphismProperty Functor.mapDerivedCategoryPlus
  etaleConstant proConstant etaleSupported proSupported
attribute [local implicit_reducible] SupportedConstantNormalization.gamma
  SupportedConstantNormalization.adj
attribute [local irreducible] ProEtale.lowerStarComparisonUpperStarBaseChange
attribute [local implicit_reducible] ProEtale.comparisonUpperStar Etale.lowerStar
  ProEtale.lowerStar Etale.upperStar ProEtale.upperStar
  ProEtale.lowerStarCompComparisonLowerStarIso
attribute [local irreducible] Etale.upperStarLowerStarAdjunction
  ProEtale.upperStarLowerStarAdjunction
private theorem comparison_gamma [Finite A] {B X : Scheme.{u}} (s : B ⟶ X) :
    SupportedConstantNormalization.gamma A s =
      (ProEtale.lowerStarComparisonUpperStarBaseChange s (ModuleCat.{u + 1} A)).app
          (SupportedConstantNormalization.constant A false B) ≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} A) s).map
          (SupportedConstantNormalization.compareUnit A B).hom := by
  let F := SupportedConstantNormalization.constant A false B
  have hm := mateEquiv_counit_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s)
    (ProEtale.lowerStarComparisonUpperStarBaseChange s (ModuleCat.{u + 1} A)) F
  have hi := iterated_mateEquiv_conjugateEquiv_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s)
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X)
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) B)
    (ProEtale.lowerStarCompComparisonLowerStarIso s (ModuleCat.{u + 1} A)).inv
  unfold ProEtale.lowerStarComparisonUpperStarBaseChange at hm
  rw [hi] at hm
  have hd : ProEtale.supportSiteComparisonCoefficientDirectImageIso
      (ModuleCat.{u + 1} A) s =
      ProEtale.lowerStarCompComparisonLowerStarIso s (ModuleCat.{u + 1} A) := by
    have hw : ProEtale.supportSiteComparisonSiteBaseChangeIso s =
        ProEtale.toProEtCompOverPullbackIso s := by
      ext M
      rfl
    dsimp only [ProEtale.supportSiteComparisonCoefficientDirectImageIso,
      ProEtale.lowerStarCompComparisonLowerStarIso]
    rw [hw]
  have ht : (SupportedConstantNormalization.comparePullback A s).inv =
      (conjugateEquiv
        ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s).comp
          (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) B))
        ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).comp
          (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s))).symm
        (ProEtale.lowerStarCompComparisonLowerStarIso s (ModuleCat.{u + 1} A)).inv := by
    with_unfolding_all
      simp only [SupportedConstantNormalization.comparePullback,
        ProEtale.supportSiteComparisonCoefficientPullbackIso, hd]
      rfl
  dsimp only [Equiv.trans_apply, TwoSquare.equivNatTrans] at hm
  erw [← ht] at hm
  symm
  exact SupportedConstantNormalization.normalized_closed_exchange
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) B)
    (SupportedConstantNormalization.comparePullback A s).symm
    (ProEtale.lowerStarComparisonUpperStarBaseChange s (ModuleCat.{u + 1} A)) F
    (SupportedConstantNormalization.compareUnit A B).hom (by
      simpa only [ProEtale.lowerStarComparisonUpperStarBaseChange, Iso.symm_hom] using hm)

/-- The canonical comparison on a closed supported constant is invertible.
Source: blueprint rank-one Thom proof, Step 3; Stacks Tag 095L
(blueprint: lem-pur-section-supported-comparison-iso).
Proof: the conjugate-adjunction formula identifies gamma with the component of
lowerStarComparisonUpperStarBaseChange followed by direct image of compareUnit.
The closed immersion is quasi-compact and quasi-separated, so the first factor
is invertible by pro-etale comparison for direct image. The scalar-preserving
constant unit is an isomorphism, and direct image preserves its invertibility.
Thus their composite gamma is invertible. This also covers an empty closed source. -/
theorem supported_comparison_isIso [Finite A] {B X : Scheme.{u}}
    (s : B ⟶ X) [IsClosedImmersion s] :
    IsIso (SupportedConstantNormalization.gamma A s) := by
  with_unfolding_all
    rw [comparison_gamma]
    let := ProEtale.isIso_lowerStarComparisonUpperStarBaseChange s (ModuleCat.{u + 1} A)
    exact (((asIso (ProEtale.lowerStarComparisonUpperStarBaseChange s
      (ModuleCat.{u + 1} A))).app (SupportedConstantNormalization.constant A false B)) ≪≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) s).mapIso
        (SupportedConstantNormalization.compareUnit A B)).isIso_hom

end AlgebraicGeometry.SectionCompactSource
