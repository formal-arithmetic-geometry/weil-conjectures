/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTensorRestrictionIso
public import WeilConjectures.AlgebraicGeometry.OpenDerivedAdditiveStalkIso
import WeilConjectures.AlgebraicGeometry.OpenStalkRepresentativeCoherence
import WeilConjectures.AlgebraicGeometry.OpenTensorRestrictionRepresentative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry
open SingleComplexBaseChange

attribute [local irreducible] tensorStalkIso tensorComplex openPinnedTensorRestrictionIso
attribute [local irreducible] openDerivedAdditiveStalkIso comparisonStalkHomologyIso

end AlgebraicGeometry
