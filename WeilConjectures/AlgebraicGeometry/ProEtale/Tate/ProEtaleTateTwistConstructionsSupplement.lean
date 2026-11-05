/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistLevelsSupplement

import all WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistLevelsSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.CategoryTheory.Filtered.Final
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistConstructions

/-! # Coefficient extension maps, the field colimit and signed Tate twists

Source: blueprint `sk-def-sp-tate-twist`. The finite levels and integral and
rational objects are re-exported from `ProEtaleTateTwistLevels`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance 20000] HasLimitsOfShape.has_limit HasColimitsOfShape.has_colimit
attribute [local instance 20000] Sheaf.instHasLimitsOfShape AddCommGrpCat.hasLimitsOfShape

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

attribute [local irreducible] spEllPointReduction spEllPointTransition

attribute [local irreducible] spIntegersMap

attribute [local instance] spEllReduction_isMonHom

attribute [local irreducible] spEllMap

attribute [local irreducible] spIntegralTwistMap

attribute [local irreducible] spRationalTwistMap

attribute [local irreducible] spIntegralTwist spIntegralTwistSystem

end AlgebraicGeometry.ProEtale
