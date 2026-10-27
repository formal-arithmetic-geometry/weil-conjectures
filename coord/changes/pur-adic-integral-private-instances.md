# CategoryTheory.purAdicIntegralComparison_exists

## Reason

The complete proof introduces a private smallness instance for its private dependent-sum
presheaf and locally registers three existing, proved sheaf-composition instances.
The latter avoid repeated expensive instance searches on essentially small sites.
The preflight classifies the instance/attribute commands as requiring a change record.
No public signature, public import, definition or importer-visible instance is changed.
The reader should verify the `private` and `local` scopes of the commands below.

## Old

There was no `sigmaSmall` declaration or local registration in this module.
The public theorem had the identical signature and a `sorry` proof.
The two backward-elaboration options below were absent.

## New

The following file-local elaboration options support the proof. They introduce no
instances or attributes visible to importers:

```lean
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
```

```lean
attribute [local instance 2000] purAdicHasSheafComposeRingSets
  purAdicHasSheafComposeModuleSets purAdicHasSheafComposeCoefficients
```

```lean
private instance sigmaSmall {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {V : C} (H : (Over V)ᵒᵖ ⥤ Type w) :
    FunctorToTypes.Small.{w} (sigmaPresheaf H) := fun X ↦ by
  dsimp [sigmaPresheaf]
  infer_instance
```

All names used only to implement the proof are private. Their definitions have complete
bodies. The theorem signature remains byte-identical to the original. These commands
only supply instance synthesis inside the file; the delivery's sole public theorem
is the original theorem, now proved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PurAdicIntegralComparison | A7 | Proves the existing theorem using private and local helpers. |
| Sheaf.Paper.PurAdicLineSystemBaseChange | unclaimed in current local claim records | Calls the unchanged public theorem; no adaptation or changed meaning. |

`tools/downstream.py Sheaf.Paper.PurAdicIntegralComparison --uses
purAdicIntegralComparison_exists` lists exactly the consumer above in addition to
the declaring module. No target or definition is changed; no statement review is reopened.

## Status

landed 20261023T230349-L-3418401 2026-10-23 (merge of deliver/A7/Sheaf.Paper.PurAdicIntegralComparison)
