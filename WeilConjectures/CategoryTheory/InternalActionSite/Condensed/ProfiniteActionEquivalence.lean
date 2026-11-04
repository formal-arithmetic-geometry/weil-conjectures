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
      ((groupPresheafUpEquiv G S) a) m⟩

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

variable (N : SiteEquivariant A G)

/-- The sheaf of modules on `Profinite` underlying an equivariant sheaf on the small model. -/
noncomputable def fromSiteSheaf :
    SheafOfModules.{u + 1} ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat RingCat)).obj
        (InternalAbelianSheafModule.sectionRingSheaf (coherentTopology Profinite.{u}) A.X)) where
  val := (PresheafOfModules.pushforward₀ (AsSmall.up : Profinite.{u} ⥤ Model.{u}) _).obj N.obj.val
  isSheaf := Functor.op_comp_isSheaf (AsSmall.up : Profinite.{u} ⥤ Model.{u})
    (coherentTopology Profinite.{u}) _ ⟨N.obj.val.presheaf, N.property⟩

/-- The internal module underlying an equivariant sheaf on the small model. -/
noncomputable def fromSiteModule : Modules A :=
  InternalAbelianSheafModule.liftedSheafModule _ A.X (fromSiteSheaf N)

/-- The section module sheaf of `fromSiteModule N` is the transported sheaf. -/
noncomputable def fromSiteIso : (sectionsFunctor A).obj (fromSiteModule N) ≅ fromSiteSheaf N :=
  InternalAbelianSheafModule.sectionModuleFunctor_counit _ A.X _

/-- The sectionwise linear isomorphism given by `fromSiteIso`. -/
noncomputable def fromSiteSectionsEquiv (S : Profinite.{u}) :
    sections A (fromSiteModule N) S ≃ₗ[sectionRing A S]
      N.obj.val.obj (op ((AsSmall.up : Profinite.{u} ⥤ Model.{u}).obj S)) :=
  ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op S)).mapIso
    (fromSiteIso N)).toLinearEquiv

/-- The action on `fromSiteModule N`, conjugated from the action of `N`. -/
noncomputable def fromSiteAct (S : Profinite.{u}) :
    C(S, G) →* Module.End (sectionRing A S) (sections A (fromSiteModule N) S) :=
  (fromSiteSectionsEquiv N S).symm.conjRingEquiv.toMonoidHom.comp
    ((N.obj.action.act (op ((AsSmall.up : Profinite.{u} ⥤ Model.{u}).obj S))).comp
      (groupPresheafUpEquiv G S).toMonoidHom)

theorem fromSiteAct_apply (S : Profinite.{u}) (g : C(S, G))
    (m : sections A (fromSiteModule N) S) :
    fromSiteAct N S g m = (fromSiteSectionsEquiv N S).symm
      (N.obj.action.act _ ((groupPresheafUpEquiv G S) g) (fromSiteSectionsEquiv N S m)) :=
  rfl

/-- An equivariant sheaf on the small model, read as an internal action. -/
noncomputable def fromSite : Equivariant A G where
  module := fromSiteModule N
  act := fromSiteAct N
  naturality S T f g m := by
    let c := fromSiteIso N
    have h1 := PresheafOfModules.naturality_apply c.inv.val f.op
      (N.obj.action.act (op ((AsSmall.up : Profinite.{u} ⥤ Model.{u}).obj S))
        ((groupPresheafUpEquiv G S) g) (c.hom.val.app (op S) m))
    have h2 := N.obj.action.naturality ((AsSmall.up : Profinite.{u} ⥤ Model.{u}).map f).op
      ((groupPresheafUpEquiv G S) g) (c.hom.val.app (op S) m)
    have h3 := PresheafOfModules.naturality_apply c.hom.val f.op m
    exact h1.symm.trans ((congrArg (c.inv.val.app (op T)) h2).trans
      (congrArg (fun x ↦ c.inv.val.app (op T) (N.obj.action.act _ _ x)) h3.symm))


/-- Reading `fromSite N` on the small model recovers `N`. -/
noncomputable def toSiteFromSiteIso : toSite.obj (fromSite N) ≅ N where
  hom := ObjectProperty.homMk (X := toSite.obj (fromSite N)) (Y := N)
    ⟨{ app X := (fromSiteIso N).hom.val.app
          (op ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop))
       naturality f := (fromSiteIso N).hom.val.naturality
          ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).map f.unop).op },
      fun X a m ↦ (fromSiteSectionsEquiv N _).apply_symm_apply _⟩
  inv := ObjectProperty.homMk (X := N) (Y := toSite.obj (fromSite N))
    ⟨{ app X := (fromSiteIso N).inv.val.app
          (op ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop))
       naturality f := (fromSiteIso N).inv.val.naturality
          ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).map f.unop).op },
      fun X a m ↦
        let e := fromSiteSectionsEquiv N ((AsSmall.down : Model.{u} ⥤ Profinite.{u}).obj X.unop)
        congrArg (fun y ↦ e.symm (N.obj.action.act X a y)) (e.apply_symm_apply m).symm⟩
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    ext X m
    exact (fromSiteSectionsEquiv N _).symm_apply_apply m
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    ext X m
    exact (fromSiteSectionsEquiv N _).apply_symm_apply m

variable (A G) in
/-- Reading internal actions on the small model is an equivalence. -/
instance toSite_isEquivalence : (toSite (A := A) (G := G)).IsEquivalence where
  faithful := toSiteFullyFaithful.faithful
  full := toSiteFullyFaithful.full
  essSurj := ⟨fun N ↦ ⟨fromSite N, ⟨toSiteFromSiteIso N⟩⟩⟩

variable (A G) in
/-- Internal actions of `G` on internal `A`-modules are equivariant sheaves of modules on the
small profinite site, keeping sections, restrictions and actions. -/
noncomputable def siteEquivalence : Equivariant A G ≌ SiteEquivariant A G :=
  (toSite (A := A) (G := G)).asEquivalence

/-- Reading internal actions on the small model is additive. -/
instance toSite_additive : (toSite (A := A) (G := G)).Additive where
  map_add := rfl

end CategoryTheory.CondensedBar.ActionSite
