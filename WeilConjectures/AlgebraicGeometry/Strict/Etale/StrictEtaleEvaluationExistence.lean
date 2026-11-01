/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemInterfaces
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedExtension
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedAbove
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedBelow
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedTransition
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientTensorDerivedUnit

/-! # Strict étale evaluation for arbitrary coefficient parameters

Source: Zheng, Construction 4.1, printed p. 21.
The existing component constructions require neither regularity nor completeness.
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
