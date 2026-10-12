# etaleGeneratorsPullbackSection and its restriction/scalar laws

## Reason

The existing theorem is reduced to restriction naturality of an explicit section
construction. The scalar law is proved using existing upstream lemmas. These are
new declarations in three new modules. No existing statement, definition, public
import, or file-level option is changed in the item module.

## Old

The three declarations did not exist. The signature of
`AlgebraicGeometry.Scheme.Modules.exists_etale_generators_pullback_unit_map`
is unchanged byte for byte.

## New

The new construction is written out below; its data contain no sorry. Its local
comparison uses the proved `nonempty_tensorPullbackAdjunction` and Mathlib
`Adjunction.leftAdjointUniq`, without adding a duplicate public comparison definition.
The following two laws describe restriction and scalar compatibility, respectively.
Only the restriction law remains sorry.

```lean
noncomputable def etaleGeneratorsPullbackSection
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u} L]
    [SheafOfModules.IsInvertible.{u, u, u} ((tensorPullback f).obj L)]
    (W : X.Etale) (s : (etaleIsoTorsor L).sheaf.obj.obj (op W)) :
    (etaleIsoTorsor ((tensorPullback f).obj L)).sheaf.obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)) := by
  haveI : IsIso s.down.1 := s.down.2
  let comparison : tensorPullback f ≅ pullback f :=
    (Classical.choice (nonempty_tensorPullbackAdjunction f)).leftAdjointUniq
      (pullbackPushforwardAdjunction f)
  let p := Limits.pullback.fst W.hom f
  let q := Limits.pullback.snd W.hom f
  let e : (pullback q).obj (unit Y) ≅
      (pullback q).obj ((tensorPullback f).obj L) :=
    pullbackObjUnitIso q ≪≫ (pullbackObjUnitIso p).symm ≪≫
      (pullback p).mapIso (pullbackObjUnitIso W.hom).symm ≪≫
      (pullback p).mapIso (asIso s.down.1) ≪≫
      (pullbackComp p W.hom).app L ≪≫
      (pullbackCongr Limits.pullback.condition).app L ≪≫
      ((pullbackComp q f).app L).symm ≪≫
      (pullback q).mapIso (comparison.app L).symm
  exact ⟨⟨e.hom, (inferInstance : IsIso e.hom)⟩⟩

```

```lean
theorem etaleGeneratorsPullbackSection_naturality {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} L] [SheafOfModules.IsInvertible.{u, u, u} ((tensorPullback f).obj L)] {V W : X.Etale} (i : V ⟶ W) (s : (etaleIsoTorsor L).sheaf.obj.obj (op W)) : (etaleIsoTorsor ((tensorPullback f).obj L)).sheaf.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ f).map i).op (etaleGeneratorsPullbackSection f L W s) = etaleGeneratorsPullbackSection f L V ((etaleIsoTorsor L).sheaf.obj.map i.op s)
```

```lean
theorem etale_generators_pullback_map_unit_formula {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} L] [SheafOfModules.IsInvertible.{u, u, u} ((tensorPullback f).obj L)] : ∀ (W : X.Etale) (g : X.gmSheaf.obj.obj (op W)) (s : (etaleIsoTorsor L).sheaf.obj.obj (op W)), (etaleGeneratorsPullbackSection f L W ((etaleIsoTorsor L).vadd (op W) g s)) = (etaleIsoTorsor ((tensorPullback f).obj L)).vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)) ((upperStarGmSheafToGmSheaf f).hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)) (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app X.gmSheaf).hom.app (op W) g)) (etaleGeneratorsPullbackSection f L W s)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackUnitMap | A3 | uses the construction and both laws only in its proof; its public signature is unchanged |
| Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackSectionsNatural | A3 | new restriction law for the new explicit construction |
| Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackMapUnitFormula | A3 | new proved scalar law for the new explicit construction |
| Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackEquivariant | none | existing caller of the unchanged existence theorem; no adaptation required |

The new modules have no existing importers on the repository baseline. No target
statement depends on a changed definition, since no existing definition changes.

## Status

landed 20261012T112829-L-763854 2026-10-12 (merge of deliver/A3/Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackUnitMap)
