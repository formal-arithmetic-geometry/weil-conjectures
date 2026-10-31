/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.RationalSmoothPurityCanonical.RationalSmoothPurityFiniteTrace

/-! # Realization and unit conventions for the finite tensor mate

Source: latest def-pur-smooth-purity-map and def-pur-smooth-trace.
(blueprint: lem-pur-canonical-realization-tensor-unit).
-/

set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme CategoryTheory.Endofunctor MonoidalCategory
namespace WeilConjectures

namespace RationalSmoothPurityCanonical

attribute [local instance 3000] instCategoryDerivedCategory ScalarLocalization.category

attribute [local instance 0] ConstructibleExceptionalCoefficients.category

attribute [local irreducible] sfIntrinsicModuleEquivalence ProEtale.comparisonUpperStar
  Functor.mapDerivedCategory HasDerivedCategory.standard

/-- The exceptional tensor mate at the realized coefficient unit, in the fixed
constant-section pullback and tensor-unit conventions.
Source: latest smooth-purity model paragraph; lem-pur-smooth-tensor-mate-unit
(blueprint: lem-pur-canonical-realization-tensor-unit).
Proof: apply smoothPurityTheta_unit to the ordinary coefficient unit. Its pullback
unit composite agrees with finitePullUnit at the identity presentation: the site
pullback square preserves the constant section, and the exact-to-derived pullback
comparison preserves its monoidal unit. Tensor comparison preserves the left
unitor, so the specified finiteTensorUnit is the same unit constraint. Finally
transport the presentation by the unit isomorphism of sfIntrinsicDerivedEquivalence.
Naturality of smoothPurityPullbackComparison puts its inverse in finitePullUnit;
naturality of smoothPurityExceptionalComparison puts its forward map after the
exceptional mate. The comparison adjunction triangle cancels the intervening unit
and counit. This gives the displayed equation. No diagonal orientation, smoothness,
relative dimension, compact-support pushforward, or trace is involved. -/
theorem finiteUnitThetaFormula (Q : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    Q.smoothPurityTheta f
      ((sfIntrinsicDerivedEquivalence Y Q.Ring).inverse.obj (Q.coefficientUnit Y))
      (Etale.ordinaryFiniteUnit Q.Coefficient Y)
      ((sfIntrinsicDerivedEquivalence Y Q.Ring).unitIso.app
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Q.Coefficient)
          Y).mapDerivedCategory.obj (Etale.ordinaryFiniteUnit Q.Coefficient Y))) =
      ((((PurityFiniteSetting.smoothPurityTensor Q.Coefficient X).mapIso
        (finitePullUnit Q f)).app (Q.diagonalDualizing f) ≪≫
          finiteTensorUnit Q.Coefficient X (Q.diagonalDualizing f)).hom) ≫
        (Q.diagonalDualizingComparison f).hom ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Q.Coefficient)
          X).mapDerivedCategory.map
          ((Etale.rightDerivedUpperShriek Q.Coefficient f).map
            ((ProEtale.derivedComparisonAdjunction
              (ModuleCat.{u + 1} Q.Coefficient) Y).unit.app
              (Etale.ordinaryFiniteUnit Q.Coefficient Y))) ≫
        (Q.smoothPurityExceptional f).map
          ((sfIntrinsicDerivedEquivalence Y Q.Ring).unitIso.hom.app
            ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Q.Coefficient)
              Y).mapDerivedCategory.obj (Etale.ordinaryFiniteUnit Q.Coefficient Y))) := by
  sorry

end RationalSmoothPurityCanonical
end WeilConjectures
