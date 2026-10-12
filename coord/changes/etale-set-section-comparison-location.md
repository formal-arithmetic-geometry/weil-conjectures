# AlgebraicGeometry.etaleSetSectionComparison

## Reason

The new coherence and descent statements must refer to the section comparison without
importing the theorem that uses them. Relocate its existing definition to a standalone
module and publicly import that module from the original. This also replaces repeated
expanded adjunction expressions whose elaboration was expensive. Its data and type do
not change; no target's meaning or statement changes.

## Old

Location: `Sheaf.AlgebraicGeometry.EtaleSetSectionContinuity`.

```lean
noncomputable def etaleSetSectionComparison
    {R S T : Scheme.{u}} (h : T ⟶ S) (f : S ⟶ R) (k : T ⟶ R) (hk : h ≫ f = k)
    (G : Sheaf R.smallEtaleTopology (Type (u + 1))) (U : R.Etale) :
    ((Scheme.etaleSetPullback f).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)) ⟶
      ((Scheme.etaleSetPullback k).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj U)) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
      (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)).unit.app
        ((Scheme.etaleSetPullback f).obj G)).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)) ≫
    ((Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S T f h).hom.app G).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))) ≫
    (eqToHom (congrArg (fun a : T ⟶ R ↦ (Scheme.etaleSetPullback a).obj G) hk)).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))) ≫
    ((Scheme.etaleSetPullback k).obj G).obj.map
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f k hk.symm).hom.app U).op
```

## New

Location: `Sheaf.AlgebraicGeometry.EtaleSetSectionComparison`, publicly reexported by
`Sheaf.AlgebraicGeometry.EtaleSetSectionContinuity`.

```lean
noncomputable def etaleSetSectionComparison
    {R S T : Scheme.{u}} (h : T ⟶ S) (f : S ⟶ R) (k : T ⟶ R) (hk : h ≫ f = k)
    (G : Sheaf R.smallEtaleTopology (Type (u + 1))) (U : R.Etale) :
    ((Scheme.etaleSetPullback f).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)) ⟶
      ((Scheme.etaleSetPullback k).obj G).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj U)) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
      (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)).unit.app
        ((Scheme.etaleSetPullback f).obj G)).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)) ≫
    ((Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S T f h).hom.app G).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))) ≫
    (eqToHom (congrArg (fun a : T ⟶ R ↦ (Scheme.etaleSetPullback a).obj G) hk)).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))) ≫
    ((Scheme.etaleSetPullback k).obj G).obj.map
      ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) h f k hk.symm).hom.app U).op
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleSetSectionContinuity --uses
etaleSetSectionComparison` lists no external modules that mention this name.
All existing consumers retain access through the public import. The original theorem
uses exactly the same definition. The direct importer is included for clarity.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleSetSectionContinuity | T1 | Same name, type, and body; public import replaces local declaration. |
| Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization | unchanged | Public reexport preserves access; no signatures or source edits needed. |

## Status

landed 20261012T053955-L-2646381 2026-10-12 (merge of deliver/T1/Sheaf.AlgebraicGeometry.EtaleSetSectionContinuity)
