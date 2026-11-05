/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleConstruction
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleLinearCriterion
import WeilConjectures.AlgebraicGeometry.EtaleModuleRingIsoAdjunction
import WeilConjectures.AlgebraicGeometry.EtaleModuleRingIsoTensor

/-!
# Transport of the etale module inverse image

Source: Stacks Project, Modules on Sites, Tags 03D2, 03D3, 03D6, 03D7, 04JC;
Sites and Sheaves, Example 0H7J
(blueprint: lem-weil-pbc-etale-module-inverse-image-transport).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry

end AlgebraicGeometry
