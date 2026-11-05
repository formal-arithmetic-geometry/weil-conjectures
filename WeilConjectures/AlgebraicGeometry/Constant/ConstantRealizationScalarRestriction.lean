/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientLocalHomologyModels
import WeilConjectures.AlgebraicGeometry.Constant.ConstantRealizationScalarRestrictionUnderlying

/-! # Constant realization and scalar restriction

Source: Stacks Project, Modules on Sites, Tags 03CY and 03EL.
(blueprint: lem-weil-pbc-constant-realization-scalar-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
universe t uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

end AlgebraicGeometry.Scheme
