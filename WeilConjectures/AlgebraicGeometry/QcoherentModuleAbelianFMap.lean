/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QcoherentZariskiCohomologyMap
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtHMap
import WeilConjectures.AlgebraicGeometry.ModuleAbelianLargeResolutionFormula
import WeilConjectures.AlgebraicGeometry.ModuleAbelianUniverseHMap

/-! # Module h-maps and abelian Zariski h-maps
Source: Stacks Project, Tags 01FB and 03FD.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] tensorPullback tensorPullbackObj
  moduleAbelianCohomologyLarge zariskiModuleHMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The fixed common-resolution comparison carries the module h-map to the
explicit abelian inverse-image Ext map. No quasi-coherence or comparisons with
etale cohomology are involved.

Source: Stacks Project, Cohomology, Tag 01FB; Cohomology on Sites, Tag 03FD.
(blueprint: lem-pbc-module-abelian-hmap).

Proof: Resolve F and G by module injectives. Use the chosen injective replacement
of the pushforward target resolution in ModuleCohomologyFMapData. Forget scalars
and lift the two module resolutions to abelian injective resolutions over their
augmentations. Injective modules are acyclic for underlying abelian sections,
so the global-section comparisons are quasi-isomorphisms. Exact abelian inverse
image gives a resolution of the pulled-back underlying F; lift its adjoint
coefficient map to the abelian target resolution. The two resulting maps to an
abelian injective replacement agree over F, hence are homotopic. Apply sections
and homology, use the fixed common-resolution normalization, and cancel the
replacement quasi-isomorphisms. Constant-integer comparison identifies this map
with zariskiModuleHMap. Canonical Ext universe change preserves the represented
morphism and commutes with composition. This proves the formula also in degree
zero, for the empty scheme, and for zero modules. -/
theorem moduleAbelianCohomologyLarge_hmap {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) (φ : F ⟶ (pushforward g).obj G)
    (q : ℕ) (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F) :
    moduleAbelianCohomologyLarge Y G q (moduleCohomologyFMap g φ q x) =
      zariskiModuleHMap g φ q (moduleAbelianCohomologyLarge X F q x) := by
  have h := moduleCohomologyExtResolutionEquiv_hmap g F G φ q x
  exact (moduleAbelianCohomologyLarge_resolutionFormula Y G q _).trans
    ((congrArg (moduleAbelianUniverseMap Y G q) h).trans
      ((moduleAbelianUniverseMap_hmap g F G φ q _).trans
        (congrArg (zariskiModuleHMap g φ q)
          (moduleAbelianCohomologyLarge_resolutionFormula X F q x).symm)))

end
end AlgebraicGeometry.Scheme.Modules
