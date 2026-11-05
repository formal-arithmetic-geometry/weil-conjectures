/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GaloisActionUnitTransportInputs

/-!
# Unit transports under a change of left adjoints

Towards the identity of `ProEtale.CondensedRing.galoisAction_eq_unitTransport_of_counit`, this
file shows that the unit transport `Fg(η_s) ≫ r ≫ Fsg(c⁻¹)` along a composition isomorphism
`r : Fs ⋙ Fg ⟶ Fsg` of right adjoints does not depend on the choice of left adjoints, up to the
comparisons `Adjunction.leftAdjointUniq`
(`CategoryTheory.unitTransport_app_leftAdjointUniq`), using that the conjugate `c` of `r`
transforms accordingly (`CategoryTheory.conjugateEquiv_symm_leftAdjointUniq`). For pro-étale
sheaves along weakly étale morphisms this replaces the pullbacks `g^*` by the restrictions
`j_g^*` along the localization functors, on which the unit transport is computed on sections.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

end CategoryTheory

