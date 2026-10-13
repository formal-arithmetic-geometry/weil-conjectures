# RingedModuleSkyscraper shared construction

## Reason

The original bundled skyscraper presheaf and sheaf proof duplicated the same membership-indexed
construction needed by the scheme module. A coefficient-type construction lets the bundled
ringed-space API provide the shared implementation while preserving its existing names.

## Old

```lean
variable (X : RingedSpace.{u_sky}) (x : X)

abbrev RingedSkyscraperSections (M : ModuleCat.{u_sky} (X.presheaf.stalk x))
    (V : Opens X) : Type u_sky := PLift (x ∈ V) → M

abbrev ringedSkyscraperPresheafAb (M : ModuleCat.{u_sky} (X.presheaf.stalk x)) :
    (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u_sky} where
  obj V := AddCommGrpCat.of (RingedSkyscraperSections X x M V.unop)
  map f := AddCommGrpCat.ofHom
    { toFun := fun s h ↦ s ⟨f.unop.le h.down⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

theorem ringedSkyscraperPresheafAb_isSheaf
    (M : ModuleCat.{u_sky} (X.presheaf.stalk x)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (ringedSkyscraperPresheafAb X x M) := by
  classical
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
    (ringedSkyscraperPresheafAb X x M)).mpr
  intro ι U sf hsf
  choose index index_spec using fun h : PLift (x ∈ iSup U) ↦ Opens.mem_iSup.mp h.down
  let s : RingedSkyscraperSections X x M (iSup U) :=
    fun h ↦ sf (index h) ⟨index_spec h⟩
  refine ⟨s, ?_, ?_⟩
  · intro i
    funext h
    exact congrFun (hsf (index ⟨(Opens.leSupr U i).le h.down⟩) i)
      ⟨⟨index_spec ⟨(Opens.leSupr U i).le h.down⟩, h.down⟩⟩
  · intro t ht
    funext h
    exact congrFun (ht (index h)) ⟨index_spec h⟩

noncomputable abbrev ringedModuleSkyscraper
    (M : ModuleCat.{u_sky} (X.presheaf.stalk x)) : SheafOfModules.{u_sky}
      ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u_sky} RingCat.{u_sky})).obj X.sheaf) where
  val := PresheafOfModules.ofPresheaf (ringedSkyscraperPresheafAb X x M)
    (fun {_ _} f a s ↦ ringedSkyscraperPresheafAb_smul X x M f a s)
  isSheaf := ringedSkyscraperPresheafAb_isSheaf X x M

noncomputable def ringedModuleSkyscraperFunctor :
    ModuleCat.{u_sky} (X.presheaf.stalk x) ⥤ SheafOfModules.{u_sky}
      ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u_sky} RingCat.{u_sky})).obj X.sheaf) where
  obj M := ringedModuleSkyscraper X x M
  map f := ringedModuleSkyscraperMap X x f
  map_id := ringedModuleSkyscraperMap_id X x
  map_comp f g := ringedModuleSkyscraperMap_comp X x f g
```

## New

```lean
variable (X : RingedSpace.{u_sky, u_sky}) (x : X)

abbrev RingedSkyscraperSections (M : ModuleCat.{u_sky} (X.presheaf.stalk x))
    (V : Opens X) : Type u_sky := ringedSkyscraperSectionsType X x M V

abbrev ringedSkyscraperPresheafAb (M : ModuleCat.{u_sky} (X.presheaf.stalk x)) :
    (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u_sky} := ringedSkyscraperPresheafAbOfType X x M

theorem ringedSkyscraperPresheafAb_isSheaf
    (M : ModuleCat.{u_sky} (X.presheaf.stalk x)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (ringedSkyscraperPresheafAb X x M) :=
  ringedSkyscraperPresheafAbOfType_isSheaf X x M

noncomputable abbrev ringedModuleSkyscraper
    (M : ModuleCat.{u_sky} (X.presheaf.stalk x)) : SheafOfModules.{u_sky, u_sky}
      ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u_sky} RingCat.{u_sky})).obj X.sheaf) where
  val := PresheafOfModules.ofPresheaf (ringedSkyscraperPresheafAb X x M)
    (fun {_ _} f a s ↦ ringedSkyscraperPresheafAb_smul X x M f a s)
  isSheaf := ringedSkyscraperPresheafAb_isSheaf X x M

noncomputable def ringedModuleSkyscraperFunctor :
    ModuleCat.{u_sky} (X.presheaf.stalk x) ⥤ SheafOfModules.{u_sky, u_sky}
      ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u_sky} RingCat.{u_sky})).obj X.sheaf) where
  obj M := ringedModuleSkyscraper X x M
  map f := ringedModuleSkyscraperMap X x f
  map_id := ringedModuleSkyscraperMap_id X x
  map_comp f g := ringedModuleSkyscraperMap_comp X x f g
```

The new coefficient-type declarations give the section type, abelian presheaf, and sheaf
proof used by the bundled specializations. The explicit universe annotations have the same
elaborated universes as the original, checked by printing both functor signatures.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Topology.RingedModuleSkyscraper | R4 | Uses the shared coefficient-type construction. |
| Sheaf.Topology.SkyscraperComplexStalk | unclaimed | Existing bundled names remain definitionally unchanged. |
| Sheaf.Topology.SkyscraperComplexAcyclic | unclaimed | Existing functor API remains unchanged. |
| Sheaf.AlgebraicGeometry.Modules.ModuleSkyscraperStalkAdjunction | unclaimed | Existing functor API remains unchanged. |
| Sheaf.Algebra.Homology.KFlatStalkCriterion | unclaimed | Existing functor API remains unchanged. |
| Sheaf.AlgebraicGeometry.FlatSheafStalk | unclaimed | Existing bundled names and functor API remain unchanged. |
| Sheaf.Topology.SkyscraperComplex | unclaimed | Existing functor API remains unchanged. |

## Status

landed 20261013T201808-L-3976507 2026-10-13 (merge of deliver/R4/Sheaf.Topology.RingedModuleSkyscraper)
