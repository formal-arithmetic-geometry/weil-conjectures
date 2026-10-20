# AlgebraicGeometry.ModuleExtensionByZeroStalkInside

## Reason

Retire the duplicate theorem in the assigned retirement item. The adopted source library
already proves precisely the same statement as
`AlgebraicGeometry.moduleExtensionByZero_stalk_inside`. The complete signatures differ only
in the declaration name. No definitions, hypotheses, universes, germ formula or chosen
adjunction change. The source theorem and its imports and proof are preserved verbatim.

## Old

```lean
theorem ModuleExtensionByZeroStalkInside (X : RingedSpace.{u}) :
    (∀ (W : Opens X) (x : X) (hx : x ∈ W),
      ∃ e : (W.sheafOfModulesEquivOver (moduleRings X)).functor ⋙
          RingedSpace.moduleStalkFunctor (X.restrict (Opens.isOpenEmbedding W)) ⟨x, hx⟩ ⋙
          ModuleCat.restrictScalars
            (X.toPresheafedSpace.restrictStalkIso (Opens.isOpenEmbedding W) ⟨x, hx⟩).inv.hom ≅
        (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)) ⋙
          RingedSpace.moduleStalkFunctor X x,
        ∀ (G : SheafOfModules.{u} ((moduleRings X).over W)) (V : Opens W)
          (hV : (⟨x, hx⟩ : W) ∈ V)
          (s : ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj G).val.obj (op V)),
          (e.hom.app G) (TopCat.Presheaf.germ (C := Ab.{u})
              (X := (X.restrict (Opens.isOpenEmbedding W)).carrier)
              ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj G).val.presheaf
              V ⟨x, hx⟩ hV s) =
            TopCat.Presheaf.germ (C := Ab.{u}) (X := X.carrier)
              ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
                PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
                  G).val.presheaf
              ((Opens.isOpenEmbedding W).isOpenMap.functor.obj V) x ⟨⟨x, hx⟩, hV, rfl⟩
              (((Classical.choice (open_restriction_adjunction_exact X W).the project server).unit.app
                G).val.app
                (op (Over.mk (homOfLE (Set.image_subset_iff.2 (fun y _ => y.2))))) s))
```

## New

The old Sheaf module is withdrawn using `deleted.txt`; no declarations remain there. The
DAG node now records this existing source theorem (unchanged):

```lean
theorem moduleExtensionByZero_stalk_inside (X : RingedSpace.{u}) :
    (∀ (W : Opens X) (x : X) (hx : x ∈ W),
      ∃ e : (W.sheafOfModulesEquivOver (moduleRings X)).functor ⋙
          RingedSpace.moduleStalkFunctor (X.restrict (Opens.isOpenEmbedding W)) ⟨x, hx⟩ ⋙
          ModuleCat.restrictScalars
            (X.toPresheafedSpace.restrictStalkIso (Opens.isOpenEmbedding W) ⟨x, hx⟩).inv.hom ≅
        (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)) ⋙
          RingedSpace.moduleStalkFunctor X x,
        ∀ (G : SheafOfModules.{u} ((moduleRings X).over W)) (V : Opens W)
          (hV : (⟨x, hx⟩ : W) ∈ V)
          (s : ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj G).val.obj (op V)),
          (e.hom.app G) (TopCat.Presheaf.germ (C := Ab.{u})
              (X := (X.restrict (Opens.isOpenEmbedding W)).carrier)
              ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj G).val.presheaf
              V ⟨x, hx⟩ hV s) =
            TopCat.Presheaf.germ (C := Ab.{u}) (X := X.carrier)
              ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
                PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
                  G).val.presheaf
              ((Opens.isOpenEmbedding W).isOpenMap.functor.obj V) x ⟨⟨x, hx⟩, hV, rfl⟩
              (((Classical.choice (open_restriction_adjunction_exact X W).the project server).unit.app
                G).val.app
                (op (Over.mk (homOfLE (Set.image_subset_iff.2 (fun y _ => y.2))))) s))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkInside | C1 | Retired duplicate; zero holes. |

`tools/downstream.py` reports zero downstream modules. Its declaration-use search returns
only the duplicate's own declaration. A full Lean-source import and identifier search agrees:
there are no surviving imports or uses of the retired declaration. The former consumer
`Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkMaps` is absent from the current tree;
`WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkMaps` already imports the source
module and applies `moduleExtensionByZero_stalk_inside X` at line 136. It needs no adaptation.
`WeilConjectures.lean` also already imports the source module. No other module is edited.
The node attachment changes, but its statement, proof route, dependencies and unit are retained.
No target statement or definition changes, so this retirement does not reopen target semantics.

## Status

landed 20261020T131942-L-1394198 2026-10-20 (merge of deliver/C1/Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkInside)
