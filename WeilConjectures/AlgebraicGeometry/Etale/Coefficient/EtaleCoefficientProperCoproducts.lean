/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemInterfaces
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleEvaluationExistence
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownLevelRealization
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownImageRealization
import WeilConjectures.AlgebraicGeometry.Proper.ProperDerivedDirectImageCoproducts

/-! # Proper coproducts in the constant ring-sheaf coefficient presentation

Source: Stacks 0F0D; Zheng, Construction 4.1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

end AlgebraicGeometry
