/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheaf
import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
import WeilConjectures.Topology.ClosedPushforwardAbelianStalks
import WeilConjectures.Topology.InverseImageStalk
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Algebra.Category.Grp.Zero

/-! # The closed-support unit for the slice-site open extension

The slice-site extension by zero from an open `U` is supported on the closure of `U`: the unit of
the adjunction for the inclusion of the closure is an isomorphism on it.

## Implementation details

The extension by zero has zero stalks outside `U`; on the closure, the stalk map of the unit
followed by the closed-pushforward germ comparison is the inverse-image stalk isomorphism.

## References

* [Stacks Project, Tags 02UZ, 00A5 and 00AE](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat

/-- For an open `U` with closure `i : closure U → X`, the unit `G → i_* i^{-1} G` is an
isomorphism, where `G` is the slice-site extension by zero of `F|_U`. -/
theorem slice_open_extension_closure_unit_isIso
    (X : TopCat.{u}) (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        TopCat.of ↥(closure (U : Set X)) ⟶ X)).unit.app
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        ((siteExtensionByZeroPresheaf U).obj (F.over U).obj))) := by
  classical
  let P : TopCat.Presheaf AddCommGrpCat.{u} X := (siteExtensionByZeroPresheaf U).obj (F.over U).obj
  let G : TopCat.Sheaf AddCommGrpCat.{u} X :=
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj P
  let i : TopCat.of ↥(closure (U : Set X)) ⟶ X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let F' := (TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj G
  let η := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app G
  have hzero (x : X) (hx : x ∉ U) : IsZero (TopCat.Presheaf.stalk G.obj x) := by
    have hp : IsZero (P.stalk x) := by
      apply AddCommGrpCat.isZero_iff_subsingleton.mpr
      suffices hh : ∀ t : P.stalk x, t = 0 from
        ⟨fun a b ↦ (hh a).trans (hh b).symm⟩
      intro t
      obtain ⟨V, hxV, s, rfl⟩ := P.exists_germ_eq t
      have : IsEmpty (V ⟶ U) := ⟨fun f ↦ hx (f.le hxV)⟩
      change DirectSum (V ⟶ U)
        (fun φ ↦ (F.over U).obj.obj (Opposite.op (Over.mk φ))) at s
      have hs : s = 0 := Subsingleton.elim _ _
      erw [hs]
      exact map_zero _
    have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
      x AddCommGrpCat.{u} P
    exact hp.of_iso (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) P))).symm
  have hc := closedPushforwardAbelianStalks (closure (U : Set X)) isClosed_closure F'
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso η).2
  intro x
  by_cases hx : x ∈ closure (U : Set X)
  · let z : TopCat.of ↥(closure (U : Set X)) := ⟨x, hx⟩
    obtain ⟨c, hcomp, _⟩ := TopCat.Sheaf.exists_inverseImage_stalk_iso_ab i z
    have he : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map η.hom ≫
        TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} i F'.obj z =
        (c.app G).hom := by
      apply TopCat.Presheaf.stalk_hom_ext G.obj
      intro V hxV
      rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc]
      change η.hom.app (Opposite.op V) ≫
        (TopCat.Presheaf.germ
          ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).obj F'.obj) V (i z) hxV ≫
          TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} i F'.obj z) = _
      rw [TopCat.Presheaf.stalkPushforward_germ]
      ext s
      exact (hcomp G V hxV s).symm
    have := hc.2.1 z
    have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map η.hom ≫
        TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} i F'.obj z) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (TopCat.Presheaf.stalkPushforward
      AddCommGrpCat.{u} i F'.obj z)
  · exact (hzero x (fun h ↦ hx (subset_closure h))).isIso (hc.1 x hx) _

end TopCat
