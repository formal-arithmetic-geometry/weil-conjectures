/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.Topology.Sheaves.Cech

/-!
# The Godement sheaf of discontinuous sections

Let `F` be a sheaf of abelian groups on a topological space `X`. Its *Godement sheaf* is the
sheaf `U ↦ ∏_{x ∈ U} F_x` of discontinuous sections of the stalks of `F`, whose underlying
presheaf is `TopCat.Presheaf.godement`. It is flasque, its Čech complexes are exact in positive
degrees (`TopCat.Presheaf.exactAt_cechComplex_godement`), and the germ maps embed `F` into it,
functorially in `F`.

## Main definitions

- `TopCat.Sheaf.godement`: the Godement sheaf of `F`, as a functor of `F`.
- `TopCat.Sheaf.toGodement`: the natural embedding `F ⟶ godement F`.

## Main statements

- `TopCat.Sheaf.isFlasque_godement`: the Godement sheaf is flasque.
- `TopCat.Sheaf.mono_toGodement`: `F ⟶ godement F` is a monomorphism.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- The presheaf of all sections of a family of abelian groups is a sheaf. -/
lemma isSheaf_godement (S : X → Type u) [∀ x, AddCommGroup (S x)] :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (TopCat.Presheaf.godement S) := by
  change TopCat.Presheaf.IsSheaf (TopCat.Presheaf.godement S)
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  classical
  have hcompat (i j : ι) (x : X) (hi : x ∈ U i) (hj : x ∈ U j) :
      sf i ⟨x, hi⟩ = sf j ⟨x, hj⟩ :=
    congrFun (hsf i j) ⟨x, ⟨hi, hj⟩⟩
  let f : ∀ x : (⨆ i, U i : Opens X), S x := fun x ↦
    sf (Opens.mem_iSup.1 x.2).choose ⟨x, (Opens.mem_iSup.1 x.2).choose_spec⟩
  have hf (i : ι) (x : X) (hx : x ∈ U i) : f ⟨x, Opens.mem_iSup.2 ⟨i, hx⟩⟩ = sf i ⟨x, hx⟩ :=
    hcompat _ _ _ _ _
  refine ⟨f, fun i ↦ funext fun x ↦ hf i x.1 x.2, fun g hg ↦ funext fun x ↦ ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 x.2
  exact (congrFun (hg i) ⟨x, hi⟩).trans (hf i x hi).symm

/-- The Godement sheaf of a sheaf of abelian groups, as a sheaf. -/
noncomputable def godementObj (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  ⟨_, isSheaf_godement fun x : X ↦ (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.obj x : Type u)⟩

/-- The map of Godement sheaves induced by a morphism of sheaves. -/
noncomputable def godementMap {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}} (φ : F ⟶ G) : godementObj F ⟶ godementObj G :=
  ObjectProperty.homMk
    { app _ := AddCommGrpCat.ofHom (AddMonoidHom.pi fun x ↦
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.1).map φ.hom).hom.comp
          (Pi.evalAddMonoidHom _ x))
      naturality _ _ _ := rfl }

/-- The **Godement sheaf** `U ↦ ∏_{x ∈ U} F_x` of discontinuous sections of the stalks of a sheaf
of abelian groups `F`, as a functor of `F`. -/
noncomputable def godement : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u} ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    where
  obj F := godementObj F
  map φ := godementMap φ
  map_id F := by
    refine CategoryTheory.Sheaf.hom_ext (NatTrans.ext (funext fun U ↦
      AddCommGrpCat.ext fun f ↦ funext fun x ↦ ?_))
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.1).map (𝟙 F.obj) (f x) = f x
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp φ ψ := by
    refine CategoryTheory.Sheaf.hom_ext (NatTrans.ext (funext fun U ↦
      AddCommGrpCat.ext fun f ↦ funext fun x ↦ ?_))
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.1).map (φ.hom ≫ ψ.hom) (f x) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.1).map ψ.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.1).map φ.hom (f x))
    rw [CategoryTheory.Functor.map_comp]
    rfl

lemma godement_obj_obj (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) :
    (godement.obj F).obj =
      TopCat.Presheaf.godement fun x : X ↦ (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.obj x : Type u) :=
  rfl

/-- The natural embedding of a sheaf into its Godement sheaf, by the germ maps. -/
noncomputable def toGodement :
    𝟭 (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ⟶ godement where
  app F := ObjectProperty.homMk (TopCat.Presheaf.toGodement F)
  naturality F G φ := by
    refine CategoryTheory.Sheaf.hom_ext (NatTrans.ext (funext fun U ↦
      AddCommGrpCat.ext fun s ↦ funext fun x ↦ ?_))
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U.unop x.1 x.2 φ.hom s).symm

instance isFlasque_godement (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) : TopCat.Presheaf.IsFlasque (godement.obj F).obj where
  epi {U V} i := by
    classical
    rw [AddCommGrpCat.epi_iff_surjective]
    intro f
    refine ⟨fun x ↦ if hx : x.1 ∈ V.unop then f ⟨x.1, hx⟩ else 0, funext fun x ↦ ?_⟩
    change (if hx : x.1 ∈ V.unop then f ⟨x.1, hx⟩ else 0) = f x
    rw [dif_pos x.2]

instance mono_toGodement (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}) : Mono (toGodement.app F) :=
  (sheafToPresheaf _ _).mono_of_mono_map
    (inferInstanceAs (Mono (TopCat.Presheaf.toGodement F)))

end TopCat.Sheaf
