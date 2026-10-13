/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.OpenModuleStalkFunctor

/-! # Comparing open module stalks under restriction

Source: Stacks Project, Tag 00A0(3), stalks of restrictions to open subspaces.
(blueprint: lem-sc-open-module-stalk-restriction-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Restricting a module sheaf to a smaller open does not change its stalk,
with both stalks regarded as modules over the ambient scheme's stalk ring.

Source: Stacks Project, Tag 00A0(3) (restriction to an open subspace),
also for sheaves of modules as specified there.
(blueprint: lem-sc-open-module-stalk-restriction-comparison).

Proof: Apply Scheme.Modules.overMapCompOverEquiv to identify restriction on
slice sites with restriction along the open immersion V.toScheme to W.toScheme.
The neighbourhoods of x contained in V are cofinal among those contained in W.
The resulting colimit comparison on underlying abelian groups is the natural
isomorphism Scheme.Modules.restrictStalkNatIso. Its formula on germs shows that
it respects multiplication by germs of structure-sheaf sections. The composite
of the two open-immersion stalk-ring maps is the ambient stalk-ring map, so after
restriction of scalars both sides are modules over the identical ring O_X,x.
This supplies inverse linear maps and their naturality on every sheaf morphism.
The construction also applies to V=W, when the comparison is the identity. -/
theorem nonempty_openModuleStalkRestrictionComparison
    (X : Scheme.{u}) (W V : X.Opens) (hVW : V ≤ W)
    (x : X) (hxW : x ∈ W) (hxV : x ∈ V) :
    Nonempty
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hVW : V ⟶ W) ⋙ openModuleStalkFunctor X V ⟨x, hxV⟩ ≅
        openModuleStalkFunctor X W ⟨x, hxW⟩) := by sorry

end
end AlgebraicGeometry.Scheme
