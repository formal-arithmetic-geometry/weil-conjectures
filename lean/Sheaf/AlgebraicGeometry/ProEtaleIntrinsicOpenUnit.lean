/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage

/-!
# Restriction of pro-etale extension by zero

Source: Weil blueprint, order 1848, the open-closed triangle unit calculation;
Stacks Project, Tags 03DI and 09AE (blueprint: lem-exc-proetale-open-unit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The unit `M → j^* j_! M` is an isomorphism for the canonical open extension adjunction
on pro-etale module sheaves, in the intrinsic constant-coefficient presentation.
Source: Weil blueprint, order 1848; Stacks, Tags 03DI and 09AE
(blueprint: lem-exc-proetale-open-unit).

Proof plan: On an object `V` over the open subscheme, every object in a covering of `V`
is still over that open subscheme. The presheaf defining extension by zero is therefore
exactly `M` on this slice, and sheafification leaves it unchanged there. Under the
extension-by-zero adjunction (lem-weil-extension-by-zero-adjunction), this identification
sends the unit to the identity on every section. It is thus an isomorphism of module
sheaves. Canonical coefficient realization transports this calculation to the intrinsic
constant-ring module category used by def-weil-extension-by-zero; its unit and counit
are isomorphisms, so the transported unit remains invertible. -/
theorem sfIntrinsicOpenUnit_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A]
    (M : proEtaleRingModules U (proEtaleConstantRing U A)) :
    IsIso ((sfIntrinsicExtensionByZeroAdjunction j A).unit.app M) := by
  sorry

end AlgebraicGeometry.Scheme
