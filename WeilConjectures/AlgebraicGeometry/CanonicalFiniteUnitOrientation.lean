/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalSmoothPurityFiniteTrace

/-! # The finite coefficient-unit orientation before taking its trace

Source: latest def-pur-smooth-purity-map and def-pur-smooth-trace.
(blueprint: def-pur-canonical-finite-unit-orientation).
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

section RelativeOrientation
variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- The inverse diagonal orientation followed by the intrinsic realization unit.
This is an explicitly constructed arrow, before compact-support pushforward or counit.
Source: latest def-pur-smooth-purity-map, the coefficient-unit specialization;
def-pur-smooth-trace, the first displayed composite
(blueprint: def-pur-canonical-finite-unit-orientation). -/
@[irreducible]
def finiteUnitOrientation (n d : ℕ) [SmoothOfRelativeDimension d f] :
    (sfIntrinsicDerivedEquivalence X (AdicSmoothDualizing.levelSetting P n).Ring).functor.obj
        ((AdicSmoothDualizing.levelSetting P n).diagonalTwist X d) ⟶
      (sfIntrinsicDerivedEquivalence X (AdicSmoothDualizing.levelSetting P n).Ring).functor.obj
        ((@PurityFiniteSetting.smoothPurityExceptionalOver
          (AdicSmoothDualizing.levelSetting P n) X Y f
          (inferInstanceAs (IsSeparated f)) (inferInstanceAs (LocallyOfFiniteType f))
          (inferInstanceAs (QuasiCompact f)) (Y ↘ Spec (.of P.field.k))
          (inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))))
          (inferInstanceAs (QuasiCompact (Y ↘ Spec (.of P.field.k))))).obj
            ((sfIntrinsicDerivedEquivalence Y
              (AdicSmoothDualizing.levelSetting P n).Ring).inverse.obj
                ((AdicSmoothDualizing.levelSetting P n).coefficientUnit Y))) := by
  letI : HasCompactification f := c.hasCompactification
  exact (sfIntrinsicDerivedEquivalence X
    (AdicSmoothDualizing.levelSetting P n).Ring).functor.map
      ((@PurityFiniteSetting.diagonalDualizingObject
        (AdicSmoothDualizing.levelSetting P n) X Y d f
        (inferInstanceAs (IsSeparated f)) (inferInstanceAs (LocallyOfFiniteType f))
        (inferInstanceAs (QuasiCompact f)) (inferInstanceAs (SmoothOfRelativeDimension d f))
        (Y ↘ Spec (.of P.field.k))
        (inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))))
        (inferInstanceAs (QuasiCompact (Y ↘ Spec (.of P.field.k))))).inv ≫
      ((AdicSmoothDualizing.levelSetting P n).diagonalDualizingComparison f).hom ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient)
        X).mapDerivedCategory.map
        ((Etale.rightDerivedUpperShriek
          (AdicSmoothDualizing.levelSetting P n).Coefficient f).map
          ((ProEtale.derivedComparisonAdjunction
            (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient) Y).unit.app
            (Etale.ordinaryFiniteUnit
              (AdicSmoothDualizing.levelSetting P n).Coefficient Y))) ≫
        ((AdicSmoothDualizing.levelSetting P n).smoothPurityExceptional f).map
          ((sfIntrinsicDerivedEquivalence Y
            (AdicSmoothDualizing.levelSetting P n).Ring).unitIso.hom.app
              ((ProEtale.comparisonUpperStar
                (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient)
                  Y).mapDerivedCategory.obj
                    (Etale.ordinaryFiniteUnit
                      (AdicSmoothDualizing.levelSetting P n).Coefficient Y))))

end RelativeOrientation
end RationalSmoothPurityCanonical
end WeilConjectures
