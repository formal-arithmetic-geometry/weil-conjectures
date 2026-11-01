/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.RationalSmoothPurityCanonical.CanonicalFiniteUnitOrientation
import WeilConjectures.PoincareDuality.RationalSmoothPurityCanonical.CanonicalRealizationTensorUnit

/-! # Tensor normalization at the finite coefficient unit

Source: latest def-pur-smooth-purity-map and def-pur-smooth-trace.
(blueprint: lem-pur-canonical-finite-unit-tensor).
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

section ChosenPresentation

attribute [local irreducible] levelSmoothExceptionalCounit sfIntrinsicDerivedEquivalence
  PurityFiniteSetting.smoothPurityExceptional PurityFiniteSetting.smoothPurityPullback

end ChosenPresentation

end RelativeOrientation
end RationalSmoothPurityCanonical
end WeilConjectures
