/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Topology.AbelianLargeCompactOpenColimit
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Sheaves.Points
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! # Local representatives for abelian inverse images

Source: Stacks Project, Sheaves, Tags 008H and 0A32.
(blueprint: lem-weil-pbc-abelian-pullback-local-sections)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_fiber_unit
    {X Y : TopCat.{u}} (f : X ⟶ Y) (F : Y.Sheaf AddCommGrpCat.{max u v})
    (x : X) :
    let Φ := Opens.pointGrothendieckTopology x
    let Ψ := Opens.pointGrothendieckTopology (f x)
    let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f) AddCommGrpCat.{max u v} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)
    ∃ e : Ψ.sheafFiber.obj F ≅ Φ.sheafFiber.obj
      ((Functor.sheafPullbackConstruction.sheafPullback (Opens.map f)
      AddCommGrpCat.{max u v} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).obj F),
      ∀ (U : Opens Y) (hx : f x ∈ U),
        Ψ.toPresheafFiber U ⟨⟨hx⟩⟩ F.obj ≫ e.hom =
          (adj.unit.app F).hom.app (op U) ≫
            Φ.toPresheafFiber ((Opens.map f).obj U) ⟨⟨hx⟩⟩
              ((Functor.sheafPullbackConstruction.sheafPullback (Opens.map f)
      AddCommGrpCat.{max u v} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).obj F).obj := by
  dsimp only
  let Φ := Opens.pointGrothendieckTopology x
  let Ψ := Opens.pointGrothendieckTopology (f x)
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f) AddCommGrpCat.{max u v} (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)
  let a := Ψ.skyscraperSheafAdjunction (A := AddCommGrpCat.{max u v})
  let b := adj.comp Φ.skyscraperSheafAdjunction
  let e := Adjunction.leftAdjointUniq a b
  refine ⟨e.app F, ?_⟩
  intro U hx
  have hu := Adjunction.homEquiv_leftAdjointUniq_hom_app a b F
  have h := congrArg (fun q ↦ q.hom.app (op U) ≫
    Pi.π (fun _ : Ψ.fiber.obj U ↦ Φ.sheafFiber.obj
      ((Functor.sheafPullbackConstruction.sheafPullback (Opens.map f)
      AddCommGrpCat.{max u v} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).obj F)) ⟨⟨hx⟩⟩) hu
  change (((Ψ.skyscraperSheafAdjunction.homEquiv _ _)
    ((e.app F).hom)).hom.app (op U) ≫ Pi.π _ ⟨⟨hx⟩⟩) = _ at h
  have hm := Ψ.skyscraperSheafAdjunction_homEquiv_apply_hom (F := F) (e.app F).hom
  change ((Ψ.skyscraperSheafAdjunction.homEquiv F _)
      (e.app F).hom).hom = Ψ.skyscraperPresheafHomEquiv (e.app F).hom at hm
  rw [hm] at h
  replace h := (Ψ.skyscraperPresheafHomEquiv_app_π (e.app F).hom U ⟨⟨hx⟩⟩).symm.trans h
  dsimp only [b] at h
  rw [Adjunction.comp_unit_app] at h
  let H := (Functor.sheafPullbackConstruction.sheafPullback (Opens.map f)
    AddCommGrpCat.{max u v} (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)).obj F
  have hΦ : (Φ.skyscraperSheafAdjunction.unit.app H).hom.app
      (op ((Opens.map f).obj U)) ≫ Pi.π (fun _ ↦ Φ.sheafFiber.obj H) ⟨⟨hx⟩⟩ =
        Φ.toPresheafFiber ((Opens.map f).obj U) ⟨⟨hx⟩⟩ H.obj := by
    rw [← Φ.skyscraperSheafAdjunction.homEquiv_id]
    have hm' := Φ.skyscraperSheafAdjunction_homEquiv_apply_hom (F := H) (𝟙 _)
    change ((Φ.skyscraperSheafAdjunction.homEquiv H _)
      (𝟙 _)).hom = Φ.skyscraperPresheafHomEquiv (𝟙 _) at hm'
    rw [hm']
    exact (Φ.skyscraperPresheafHomEquiv_app_π (𝟙 (Φ.presheafFiber.obj H.obj))
      ((Opens.map f).obj U) ⟨⟨hx⟩⟩).trans (Category.comp_id _)
  change Ψ.toPresheafFiber U ⟨⟨hx⟩⟩ F.obj ≫ (e.app F).hom =
    ((adj.unit.app F).hom.app (op U) ≫
      (Φ.skyscraperSheafAdjunction.unit.app H).hom.app
        (op ((Opens.map f).obj U))) ≫ Pi.π _ ⟨⟨hx⟩⟩ at h
  rw [Category.assoc, hΦ] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- A section of an abelian inverse image is locally the restriction of a unit section,
including when coefficients live in a larger universe than the spaces.

Proof: The skyscraper sheaf at x, pushed along f, is the skyscraper at f(x).
The two left adjoints to this common functor are therefore canonically isomorphic:
the fiber at f(x), and inverse image followed by the fiber at x. The unit identity
for uniqueness of left adjoints gives the formula on germs. Represent the inverse
of the germ of the given section by a section on a neighborhood of f(x). The unit
formula makes its image have the required germ at x. Restrict both sections to the
intersection of their domains; filtered-colimit equality gives a smaller neighborhood
where they agree. Empty domains require no pointwise witness.
Source: Stacks Project, Sheaves, Tag 008H and Tag 0A32, local representability step.
(blueprint: lem-weil-pbc-abelian-pullback-local-sections) -/
theorem abelianPullback_localSections
    {X Y : TopCat.{u}} (f : X ⟶ Y) (F : Y.Sheaf AddCommGrpCat.{max u v})
    (U : Opens X)
    (s : ((Functor.sheafPullbackConstruction.sheafPullback (Opens.map f)
      AddCommGrpCat.{max u v} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).obj F).obj.obj (op U))
    (x : X) (hx : x ∈ U) :
    ∃ (V : Opens Y) (_ : f x ∈ V) (t : F.obj.obj (op V))
      (W : Opens X) (_ : x ∈ W) (hWU : W ≤ U) (hWV : W ≤ (Opens.map f).obj V),
      ((Functor.sheafPullbackConstruction.sheafPullback (Opens.map f)
        AddCommGrpCat.{max u v} (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).obj F).obj.map (homOfLE hWU).op s =
        ((Functor.sheafPullbackConstruction.sheafPullback (Opens.map f)
          AddCommGrpCat.{max u v} (Opens.grothendieckTopology Y)
            (Opens.grothendieckTopology X)).obj F).obj.map (homOfLE hWV).op
              (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (Opens.map f) AddCommGrpCat.{max u v} (Opens.grothendieckTopology Y)
                  (Opens.grothendieckTopology X)).unit.app F).hom.app (op V) t) := by
  let Φ := Opens.pointGrothendieckTopology x
  let Ψ := Opens.pointGrothendieckTopology (f x)
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f) AddCommGrpCat.{max u v} (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)
  let H := (Functor.sheafPullbackConstruction.sheafPullback (Opens.map f)
      AddCommGrpCat.{max u v} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).obj F
  obtain ⟨e, he⟩ := pullback_fiber_unit f F x
  obtain ⟨V, hv, t, ht⟩ := Ψ.toPresheafFiber_jointly_surjective
    ((e.inv) (Φ.toPresheafFiber U ⟨⟨hx⟩⟩ H.obj s))
  have hv' : f x ∈ V := hv.down.down
  have hg : Φ.toPresheafFiber ((Opens.map f).obj V) ⟨⟨hv'⟩⟩ H.obj
      ((adj.unit.app F).hom.app (op V) t) = Φ.toPresheafFiber U ⟨⟨hx⟩⟩ H.obj s := by
    have h := ConcreteCategory.congr_hom (he V hv') t
    change e.hom (Ψ.toPresheafFiber V ⟨⟨hv'⟩⟩ F.obj t) =
      Φ.toPresheafFiber ((Opens.map f).obj V) ⟨⟨hv'⟩⟩ H.obj
        ((adj.unit.app F).hom.app (op V) t) at h
    have hv_id : hv = ⟨⟨hv'⟩⟩ := Subsingleton.elim _ _
    change Ψ.toPresheafFiber V hv F.obj t =
      e.inv (Φ.toPresheafFiber U ⟨⟨hx⟩⟩ H.obj s) at ht
    rw [hv_id] at ht
    exact h.symm.trans ((congrArg e.hom ht).trans
      (ConcreteCategory.congr_hom e.inv_hom_id _))
  let A := U ⊓ (Opens.map f).obj V
  have hA : x ∈ A := ⟨hx, hv'⟩
  let a : A ⟶ U := homOfLE inf_le_left
  let b : A ⟶ (Opens.map f).obj V := homOfLE inf_le_right
  have hg' : Φ.toPresheafFiber A ⟨⟨hA⟩⟩ H.obj (H.obj.map a.op s) =
      Φ.toPresheafFiber A ⟨⟨hA⟩⟩ H.obj
        (H.obj.map b.op ((adj.unit.app F).hom.app (op V) t)) := by
    rw [← ConcreteCategory.comp_apply, Φ.toPresheafFiber_w,
      ← ConcreteCategory.comp_apply, Φ.toPresheafFiber_w]
    exact hg.symm
  obtain ⟨W, r, hw, _, hres⟩ := (Φ.toPresheafFiber_eq_iff' A ⟨⟨hA⟩⟩ _ _).mp hg'
  refine ⟨V, hv', t, W, hw.down.down, r.le.trans inf_le_left,
    r.le.trans inf_le_right, ?_⟩
  change H.obj.map (homOfLE (r.le.trans inf_le_left)).op s =
    H.obj.map (homOfLE (r.le.trans inf_le_right)).op
      ((adj.unit.app F).hom.app (op V) t)
  have ha : r ≫ a = homOfLE (r.le.trans inf_le_left) := Subsingleton.elim _ _
  have hb : r ≫ b = homOfLE (r.le.trans inf_le_right) := Subsingleton.elim _ _
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, ha, hb] using hres

end TopCat.Sheaf
