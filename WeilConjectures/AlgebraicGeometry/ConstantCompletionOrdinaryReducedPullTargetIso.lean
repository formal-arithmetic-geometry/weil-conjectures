/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryReducedPullSourceIso
import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryReducedPullTargetProjectionIso
import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryReducedPullTargetProjectionModelIso

/-! # Target transport for ordinary finite reduction

The target-side transport to the finite quotient model is isolated here.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion

namespace CategoryTheory.ConstantCompletion

variable {C C' : Type u} [SmallCategory C] [SmallCategory C']
variable {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)

end CategoryTheory.ConstantCompletion
