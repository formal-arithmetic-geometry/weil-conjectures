/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.Condensed.ProfiniteActionSite

/-!
# Internal condensed actions as equivariant sheaves on the small profinite site

Source: paragraph (3) of the direct-image stability proof, action-site presentation
(blueprint: def-sfb-condensed-derived-invariants).

An internal action of a topological group `G` on an internal module over a condensed ring
`A` is the same as an equivariant sheaf of modules, for the group sheaf `S ↦ C(S, G)`, over
the section ring sheaf on the small model of `Profinite`. The functor `toSite` keeps the
section modules, restrictions, actions and linear maps definitionally.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CondensedBar.ActionSite

variable (A : Ring.{u}) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The coefficient ring sheaf on the small model, as a sheaf of rings. -/
noncomputable abbrev siteRing : Sheaf modelPrecoverage.{u}.toGrothendieck RingCat.{u + 1} :=
  InternalActionSite.baseRing modelPrecoverage.toGrothendieck (ringSheaf A)

/-- Equivariant sheaves of modules on the small model for the group sheaf `C(-, G)`. -/
noncomputable abbrev SiteEquivariant :=
  InternalActionSite.EquivariantSheaf (K := groupPresheaf G) modelPrecoverage.toGrothendieck
    (siteRing A)

variable {A G}

/-- An internal action, read on the small model. -/
noncomputable def toSiteObj (M : Equivariant A G) : SiteEquivariant A G where
  obj :=
    { val := (PresheafOfModules.pushforward₀ (AsSmall.down : Model.{u} ⥤ Profinite.{u}) _).obj
        ((sectionsFunctor A).obj M.module).val
      action :=
        { act X := (M.act ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop)).comp
            (groupPresheafObjEquiv G X).toMonoidHom
          naturality f a m :=
            M.naturality _ _ ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).map f.unop) a.down m } }
  property := Functor.op_comp_isSheaf (AsSmall.down : Model.{u} ⥤ Profinite.{u}) _
    (coherentTopology Profinite.{u}) M.module.X

/-- The equivariant linear map read on the small model. -/
noncomputable def toSiteMap {M N : Equivariant A G} (f : M ⟶ N) : toSiteObj M ⟶ toSiteObj N :=
  ObjectProperty.homMk (X := toSiteObj M) (Y := toSiteObj N)
    ⟨(PresheafOfModules.pushforward₀ (AsSmall.down : Model.{u} ⥤ Profinite.{u}) _).map
      ((sectionsFunctor A).map f.val).val, fun _ a m ↦ f.property _ a.down m⟩

/-- Internal actions as equivariant sheaves on the small model. -/
noncomputable def toSite : Equivariant A G ⥤ SiteEquivariant A G where
  obj := toSiteObj
  map := toSiteMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Every equivariant map on the small model comes from an equivariant internal map. -/
noncomputable def toSitePreimage {M N : Equivariant A G} (g : toSite.obj M ⟶ toSite.obj N) :
    M ⟶ N :=
  ⟨(InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful _ A.X).preimage
      ⟨{ app S := g.hom.val.app (op ((AsSmall.up : Profinite.{u} ⥤ Model.{u}).obj S.unop))
         naturality f := g.hom.val.naturality ((AsSmall.up : Profinite.{u} ⥤ Model.{u}).map
            f.unop).op }⟩,
    fun S a m ↦ g.hom.property (op ((AsSmall.up : Profinite.{u} ⥤ Model.{u}).obj S))
      ((groupPresheafObjEquiv G _).symm a) m⟩

/-- Reading internal actions on the small model is fully faithful. -/
noncomputable def toSiteFullyFaithful : (toSite (A := A) (G := G)).FullyFaithful where
  preimage := toSitePreimage
  map_preimage g := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    ext X m
    rfl
  preimage_map f := by
    apply Subtype.ext
    apply (InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful _ A.X).map_injective
    refine ((InternalAbelianSheafModule.sectionModuleFunctor_fullyFaithful _ A.X).map_preimage
      _).trans ?_
    ext S m
    rfl

end CategoryTheory.CondensedBar.ActionSite
