/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EnlargedEtaleRingedSite

/-!
# Small coefficient modules on enlarged étale sites

Source: Stacks Project, Tags 03G1 and 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).

The original module restriction fixes a larger coefficient universe. This interface uses
exactly the same ring isomorphism and Mathlib pushforward with arbitrary module universe.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Scheme restriction with an independent module universe.
Source: Stacks, Tags 03G1 and 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def smallEnlargedModuleRestriction (X : AlgebraicSpace S) :
    ringedSiteModules.{v} X.enlargedStructureSheaf ⥤
      ringedSiteModules.{v} X.structureSheaf :=
  SheafOfModules.pushforward (enlargedStructureRestriction X).inv

/-- Restriction is an equivalence also for small module carriers.
Source: Stacks, Tags 03G1 and 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: extend the underlying abelian sheaf using a scheme atlas and the equalizer on
its scheme overlap. The equalizer is a subset of the small atlas section module, hence
has the same coefficient universe. Restriction, addition and the scalar action descend
through this equalizer. Scheme charts cover every enlarged object, so the restriction
and extension are mutually inverse, naturally on modules and on their morphisms.
This is the module argument in the original node with the coefficient bound retained. -/
theorem smallEnlargedModuleRestriction_equivalence (X : AlgebraicSpace S) :
    (smallEnlargedModuleRestriction.{u, v} X).IsEquivalence := by
  sorry

/-- Extension with its normalized restriction, using the equivalence universal property.
Source: Stacks, Tags 03G1 and 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def smallEnlargedModuleEquivalence (X : AlgebraicSpace S) :
    ringedSiteModules.{v} X.enlargedStructureSheaf ≌
      ringedSiteModules.{v} X.structureSheaf :=
  @Functor.asEquivalence _ _ _ _ (smallEnlargedModuleRestriction X)
    (smallEnlargedModuleRestriction_equivalence X)

end AlgebraicGeometry.AlgebraicSpace
