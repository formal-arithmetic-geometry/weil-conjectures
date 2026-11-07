/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersion
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedTriangle

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The open–closed triangle on the ambient derived categories of module objects

The open–closed triangle `Dj_! Lj^* K ⟶ K ⟶ Ri_* Li^* K ⟶`
(`ProEtale.CondensedRing.exists_distTriang_openClosed_derived`) is proved in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedTriangle`; this module
re-exports it together with the localizing subcategories and the closed immersion results it
used to import. If `Lj^* K = 0`, the unit `K ⟶ Ri_* Li^* K` is an isomorphism
(`ProEtale.CondensedRing.isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero`, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleClosedPushforward`).
-/
