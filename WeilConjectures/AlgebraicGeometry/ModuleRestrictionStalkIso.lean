/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.Geometry.RingedSpace.Stalks
import WeilConjectures.Algebra.Homology.ModuleRestrictionStalkComponents

/-! # Open restriction does not change a module stalk

## References

* [Stacks, Tag 00A0](https://stacks.math.columbia.edu/tag/00A0)
* [Stacks, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

set_option maxHeartbeats 400000 in
-- Identifying the slice-site restriction with the subspace presheaf unfolds colimit instances.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction to an open neighborhood preserves a module stalk after scalar transport
(Stacks, Tags 00A0 and 01CP). -/
theorem nonempty_moduleRestrictionStalk_iso
    (X : RingedSpace.{u}) (F : Modules X) (U : Opens X) (x : X) (hxU : x ∈ U) :
    Nonempty
      ((ModuleCat.restrictScalars
          (X.toPresheafedSpace.restrictStalkIso U.isOpenEmbedding ⟨x, hxU⟩).inv.hom).obj
        ((moduleStalkFunctor (X.restrict U.isOpenEmbedding) ⟨x, hxU⟩).obj
          ((U.sheafOfModulesEquivOver (moduleRings X)).functor.obj (F.over U))) ≅
        (moduleStalkFunctor X x).obj F) := by
  classical
  obtain ⟨c, hc⟩ := exists_moduleRestrictionStalk_components X U x hxU
  let S : PresheafedSpace AddCommGrpCat.{u} := ⟨X.carrier, F.val.presheaf⟩
  let N := (U.sheafOfModulesEquivOver (moduleRings X)).functor.obj (F.over U)
  -- Identify the presheaves before taking stalks, avoiding a large colimit type comparison.
  let d : N.val.presheaf ≅ (S.restrict U.isOpenEmbedding).presheaf := Iso.refl _
  let e := (TopCat.Presheaf.stalkFunctor (X := (X.restrict U.isOpenEmbedding).carrier)
      AddCommGrpCat.{u} ⟨x, hxU⟩).mapIso d ≪≫
    S.restrictStalkIso U.isOpenEmbedding ⟨x, hxU⟩
  have he (m : TopCat.Presheaf.stalk (C := Ab.{u})
      (X := (X.restrict U.isOpenEmbedding).carrier) N.val.presheaf ⟨x, hxU⟩) :
      c F m = e.hom m := by
    obtain ⟨V, hV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
      (C := Ab.{u}) (X := (X.restrict U.isOpenEmbedding).carrier) N.val.presheaf m
    have hg := TopCat.Presheaf.stalkFunctor_map_germ_apply V ⟨x, hxU⟩ hV d.hom s
    change c F (TopCat.Presheaf.germ (C := Ab.{u})
        (X := (X.restrict U.isOpenEmbedding).carrier) N.val.presheaf V ⟨x, hxU⟩ hV s) =
      (S.restrictStalkIso U.isOpenEmbedding ⟨x, hxU⟩).hom
        ((TopCat.Presheaf.stalkFunctor (X := (X.restrict U.isOpenEmbedding).carrier)
          AddCommGrpCat.{u} ⟨x, hxU⟩).map d.hom
          (TopCat.Presheaf.germ (C := Ab.{u})
            (X := (X.restrict U.isOpenEmbedding).carrier) N.val.presheaf V ⟨x, hxU⟩ hV s))
    rw [hg]
    exact (hc F V hV s).trans
      (S.restrictStalkIso_hom_eq_germ_apply U.isOpenEmbedding V ⟨x, hxU⟩ hV s).symm
  have hb : Function.Bijective (c F) := by
    have hb' := ConcreteCategory.bijective_of_isIso e.hom
    constructor
    · intro m n h
      apply hb'.1
      exact (he m).symm.trans (h.trans (he n))
    · intro m
      obtain ⟨n, hn⟩ := hb'.2 m
      exact ⟨n, (he n).trans hn⟩
  have : IsIso (c F) := (ConcreteCategory.isIso_iff_bijective (c F)).mpr hb
  exact ⟨asIso (c F)⟩

end AlgebraicGeometry.RingedSpace
