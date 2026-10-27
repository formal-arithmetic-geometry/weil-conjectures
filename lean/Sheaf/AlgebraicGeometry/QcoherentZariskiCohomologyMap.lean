/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E9
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Functors

/-! # The abelian Zariski cohomology map of a module h-map

Source: Stacks Project, Cohomology, Tags 01F8 and 01FB.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] tensorPullback tensorPullbackObj

/-- Forget the scalars in a module h-map.
Source: Stacks Project, Tag 01FB.
(blueprint: def-pbc-qcoherent-zariski-cohomology-map). -/
def moduleAbelianHMap {X Y : Scheme.{u}} (g : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (φ : F ⟶ (pushforward g).obj G) :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj F ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g.base).obj
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj G) :=
  ⟨{ app U := φ.app U.unop
     naturality _ _ h := φ.mapPresheaf.naturality h }⟩

/-- Exact abelian inverse image, the canonical constant-integer comparison, and the
adjoint coefficient map define the Zariski cohomology map. This is an explicit Ext
construction, independent of module resolutions and of etale comparisons.
Source: Stacks Project, Tags 01F8 and 01FB.
(blueprint: def-pbc-qcoherent-zariski-cohomology-map). -/
def zariskiModuleHMap {X Y : Scheme.{u}} (g : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (φ : F ⟶ (pushforward g).obj G) (q : ℕ) :
    CoherentEtale.Source X F q →+ CoherentEtale.Source Y G q := by
  let J := Opens.grothendieckTopology X
  let K := Opens.grothendieckTopology Y
  letI : HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u}) := HasExt.standard _
  letI : HasExt.{u + 1} (Sheaf K AddCommGrpCat.{u}) := HasExt.standard _
  let L := (Opens.map g.base).sheafPullback AddCommGrpCat.{u} J K
  letI := lan_preservesFiniteLimits_of_flat (E := AddCommGrpCat.{u}) (Opens.map g.base)
  letI : PreservesFiniteLimits L :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _
  letI := ((Opens.map g.base).sheafAdjunctionContinuous AddCommGrpCat.{u} J K
    ).leftAdjoint_preservesColimits
  letI : L.Additive := Functor.additive_of_preserves_binary_products L
  exact (Sheaf.H.map
    (((Opens.map g.base).sheafAdjunctionContinuous AddCommGrpCat.{u} J K).homEquiv _ _
      |>.symm (moduleAbelianHMap g φ)) q).comp
    (Sheaf.H.mapFunctor L
      (((Opens.map g.base).constantSheafsheafPullbackIso AddCommGrpCat.{u} J K
        isTerminalTop isTerminalTop).symm.app (AddCommGrpCat.of (ULift ℤ)))
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) q)

end
end AlgebraicGeometry.Scheme.Modules
