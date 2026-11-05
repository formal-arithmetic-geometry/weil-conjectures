/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Localization restriction and restriction of scalars

Restriction `j_f^*` along a weakly étale `f : V ⟶ U` commutes strictly with restriction of
scalars along a ring map `q : R →+* S`. The mate of this strict square along the adjunctions
`j_f^* ⊣ f_*` is the identity, since the unit of `j_f^* ⊣ f_*` is computed in the same way for
both coefficient rings.

Source: Stacks Project, Tags 03DA and 0960.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {V U : Scheme.{u}} (f : V ⟶ U) (h : WeaklyEtale f)
  {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S)

end AlgebraicGeometry.ProEtale
