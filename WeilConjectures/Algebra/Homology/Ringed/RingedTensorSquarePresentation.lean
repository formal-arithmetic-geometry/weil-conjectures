/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Presentations of ringed tensor squares

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 0D6D and 0E48
(blueprint: def-weil-pbc-ringed-tensor-square-presentation).
-/

@[expose] public section

set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

attribute [instance] RingedTensorCorner.category RingedTensorCorner.derived

attribute [instance] RingedTensorEdge.finiteLimits RingedTensorEdge.additive

end SheafOfModules
