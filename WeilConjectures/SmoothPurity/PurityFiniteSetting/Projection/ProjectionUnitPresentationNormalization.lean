/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionPurityCoordinates
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionPurityCoordinates
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedIntegrationTransposes
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.SmoothPurityTensorUnit
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Iso
import all Mathlib.Logic.Small.Defs
import all WeilConjectures.Compactification.Defs

/-! # Projection agreement at the coefficient unit

Source: projection-purity-agreement, final canonical reassociations.
(blueprint: lem-pur-projection-unit-presentation-normalization).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [local instance] _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

end WeilConjectures.PurityFiniteSetting
