/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.Topology.InverseImageStalk

/-! # The inverse-image structure map on stalks

## References

* Stacks Project, Tags 0098 and 0095.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory TopologicalSpace TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- The inverse-image ring stalk is the base stalk, compatibly with the structure map.
(Stacks, Tags 0098, 0095) -/
theorem exists_inverseImageStructure_stalk_iso
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    ∃ e : S.presheaf.stalk (f x) ≅
        (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).obj
        (TopCat.Sheaf.inverseImageRing f.base S.sheaf).obj,
      e.hom ≫ (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (Modules.tensorPullbackRingMap f).hom = f.stalkMap x := by
  classical
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) CommRingCat.{u} (Opens.grothendieckTopology S)
      (Opens.grothendieckTopology X)
  let a := Adjunction.leftAdjointUniq
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base) adj
  obtain ⟨c, hc, _⟩ := TopCat.Sheaf.exists_inverseImage_stalk_iso_commRing f.base x
  let d := (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).mapIso
    ((TopCat.Sheaf.forget CommRingCat.{u} X.toTopCat).mapIso (a.app S.sheaf))
  refine ⟨c.app S.sheaf ≪≫ d, ?_⟩
  apply TopCat.Presheaf.stalk_hom_ext
  intro V hxV
  ext s
  change _ = (f.stalkMap x).hom (S.presheaf.germ V (f x) hxV s)
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  have hcs := hc S.sheaf V hxV s
  change (c.app S.sheaf).hom (S.presheaf.germ V (f x) hxV s) = _ at hcs
  erw [hcs]
  dsimp [d]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base) adj S.sheaf
  have huV := congrArg (fun q ↦ q.hom.app (Opposite.op V)) hu
  have ht := adj.homEquiv S.sheaf X.sheaf
    |>.apply_symm_apply (show S.sheaf ⟶
      ((Opens.map f.base).sheafPushforwardContinuous CommRingCat.{u}
        (Opens.grothendieckTopology S) (Opens.grothendieckTopology X)).obj
        X.sheaf from ⟨f.c⟩)
  rw [Adjunction.homEquiv_unit] at ht
  have htV := congrArg (fun q ↦ q.hom.app (Opposite.op V)) ht
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rw [f.germ_stalkMap_apply]
  congr 1
  change ((Modules.tensorPullbackRingMap f).hom.app _)
    ((a.hom.app S.sheaf).hom.app _
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
        S.sheaf).hom.app (Opposite.op V)) s)) = f.app V s
  have h := congrArg (fun q ↦ q s) huV
  change (a.hom.app S.sheaf).hom.app _
    ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
      S.sheaf).hom.app (Opposite.op V)) s) =
        ((adj.unit.app S.sheaf).hom.app (Opposite.op V)) s at h
  erw [h]
  exact congrArg (fun q ↦ q s) htV

end AlgebraicGeometry.Scheme
