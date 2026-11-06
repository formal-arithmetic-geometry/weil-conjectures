/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-! # Etale locality of the ordinary ambient adjoint

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-etale-adjoint-locality.md
(blueprint: lem-amb-etale-adjoint-locality).

Sheaf-level exactness is the existing `preservesFiniteLimits_etaleLowerShriek`, together
with preservation of colimits by its existing left-adjoint structure. The first declaration
below descends the existing sheaf adjunction, without any boundedness restriction. The second
states locality for arbitrary right adjoints of the ordinary compact-support candidates.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
