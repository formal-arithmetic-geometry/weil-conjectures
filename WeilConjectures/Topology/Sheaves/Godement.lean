/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.Stalks
public import WeilConjectures.Topology.Sheaves.SubgroupOfFunctions

/-!
# The Godement sheaf of discontinuous sections

Let `F` be a sheaf of abelian groups on a topological space `X`. Its *Godement sheaf* is the
sheaf `U ↦ ∏_{x ∈ U} F_x` of discontinuous sections of the stalks of `F`. It is flasque, and the
germ maps embed `F` into it, functorially in `F`.

## Main definitions

- `TopCat.Sheaf.godement`: the Godement sheaf of `F`, as a functor of `F`.
- `TopCat.Sheaf.toGodement`: the natural embedding `F ⟶ godement F`.

## Main statements

- `TopCat.Sheaf.isFlasque_godement`: the Godement sheaf is flasque.
- `TopCat.Sheaf.mono_toGodement`: `F ⟶ godement F` is a monomorphism.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- All dependent functions into the stalks of a presheaf. -/
def godementData (F : TopCat.Presheaf AddCommGrpCat.{u} X) :
    SubgroupOfFunctions (fun x : X ↦ F.stalk x) where
  subgroup _ := ⊤
  restrict_mem _ _ _ := AddSubgroup.mem_top _
  mem_of_forall _ _ _ := AddSubgroup.mem_top _

/-- The map of Godement sheaves induced by a morphism of sheaves. -/
def godementMap {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (φ : F ⟶ G) :
    (godementData F.obj).sheaf ⟶ (godementData G.obj).sheaf :=
  ObjectProperty.homMk
    { app _ := AddCommGrpCat.ofHom
        { toFun f := ⟨fun x ↦ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.1).map φ.hom (f.1 x), AddSubgroup.mem_top _⟩
          map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
          map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _) }
      naturality _ _ _ := rfl }

/-- The **Godement sheaf** `U ↦ ∏_{x ∈ U} F_x` of discontinuous sections of the stalks of a sheaf
of abelian groups `F`, as a functor of `F`. -/
def godement : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} where
  obj F := (godementData F.obj).sheaf
  map φ := godementMap φ
  map_id F := by
    refine CategoryTheory.Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ AddCommGrpCat.ext fun f ↦ ?_))
    refine Subtype.ext (funext fun x ↦ ?_)
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.1).map (𝟙 F.obj) (f.1 x) = f.1 x
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp φ ψ := by
    refine CategoryTheory.Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ AddCommGrpCat.ext fun f ↦ ?_))
    refine Subtype.ext (funext fun x ↦ ?_)
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.1).map (φ.hom ≫ ψ.hom) (f.1 x) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.1).map ψ.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.1).map φ.hom (f.1 x))
    rw [CategoryTheory.Functor.map_comp]
    rfl

lemma godement_obj_obj (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (U : (Opens X)ᵒᵖ) :
    (godement.obj F).obj.obj U =
      AddCommGrpCat.of ((godementData F.obj).subgroup U.unop) :=
  rfl

/-- The germ maps, as a morphism from a sheaf to its Godement sheaf. -/
def toGodementApp (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : F ⟶ godement.obj F :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun s := ⟨fun x ↦ TopCat.Presheaf.germ F.obj U.unop x.1 x.2 s, AddSubgroup.mem_top _⟩
          map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
          map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _) }
      naturality U V i := by
        ext s
        refine Subtype.ext (funext fun x ↦ ?_)
        exact TopCat.Presheaf.germ_res_apply' F.obj i x.1 x.2 s }

/-- The natural embedding of a sheaf into its Godement sheaf. -/
def toGodement : 𝟭 (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ⟶ godement where
  app F := toGodementApp F
  naturality F G φ := by
    refine CategoryTheory.Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ AddCommGrpCat.ext fun s ↦ ?_))
    refine Subtype.ext (funext fun x ↦ ?_)
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U.unop x.1 x.2 φ.hom s).symm

lemma toGodement_app_apply (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (U : (Opens X)ᵒᵖ)
    (s : F.obj.obj U) (x : U.unop) :
    (show (godementData F.obj).subgroup U.unop from (toGodement.app F).hom.app U s).1 x =
      TopCat.Presheaf.germ F.obj U.unop x.1 x.2 s :=
  rfl

instance isFlasque_godement (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    TopCat.Presheaf.IsFlasque (godement.obj F).obj where
  epi {U V} i := by
    classical
    rw [AddCommGrpCat.epi_iff_surjective]
    intro f
    refine ⟨⟨fun x ↦ if hx : x.1 ∈ V.unop then f.1 ⟨x.1, hx⟩ else 0, AddSubgroup.mem_top _⟩, ?_⟩
    refine Subtype.ext (funext fun x ↦ ?_)
    change (if hx : x.1 ∈ V.unop then f.1 ⟨x.1, hx⟩ else 0) = f.1 x
    rw [dif_pos x.2]

instance mono_toGodement (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : Mono (toGodement.app F) := by
  have (U : (Opens X)ᵒᵖ) : Mono ((toGodement.app F).hom.app U) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro s t hst
    refine TopCat.Presheaf.section_ext F U.unop s t fun x hx ↦ ?_
    exact congrFun (congrArg Subtype.val hst) ⟨x, hx⟩
  have : Mono (toGodement.app F).hom := NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf _ _).mono_of_mono_map this

end TopCat.Sheaf
