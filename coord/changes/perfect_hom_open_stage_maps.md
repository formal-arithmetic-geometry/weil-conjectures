# perfect_hom_open_stage_maps proof-local elaboration commands

## Reason

The returned core and equations declarations repeated the entire item. They were unlanded
new declarations and are removed from this repair. The item now composes an explicit shifted
open adjunction equivalence with unshifted restricted representing data. Its signature and
public imports are identical to sheaf-dag. The command changes below support elaboration of
these proof-local helpers; the delivery checker conservatively classifies command changes
as an interface change. No existing definition or statement is changed.

The returned file-level `set_option linter.unusedVariables false` is deleted as requested.
It was not present in the sheaf-dag item and was incorrectly reported as removed previously.
The unchanged theorem type contains an unused let binder Z. The delivery tool refuses all
warnings, so a declaration-scoped suppression applies only to that existing theorem; lint
checks remain enabled for both new private helpers and the new restriction-data module.

## Old

The relevant sheaf-dag command sequence was:

```lean
namespace AlgebraicGeometry
```

The returned delivery additionally had the following command, now deleted:

```lean
set_option linter.unusedVariables false
```

Neither retired helper module nor its two nodes exists on sheaf-dag. Removing that unlanded
scaffolding does not remove an existing library declaration.

## New

```lean
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

noncomputable section
```

Immediately before the item's docstring, the command is scoped to this declaration:

```lean
set_option linter.unusedVariables false in
```

This handles the unchanged legacy let binder Z; it does not disable any helper's linting.
The added section is closed before the unchanged namespace end. Both added declarations
`openShiftEquiv` and `openShiftEquiv_natural` are private and fully proved. The former is a
composition of existing Hom equivalences and the latter uses their target naturality.
The new theorem `perfect_hom_open_restricted_data` and the three concrete restriction-map
constructions are in a new module with their own new DAG node; no existing signature changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PerfectHomOpenStageMaps | F1 | Item signature and public imports preserved; proof-local helpers and commands added. |
| Sheaf.AlgebraicGeometry.PerfectHomOpenStagePresentation | unclaimed | Existing call uses exactly the same theorem type; no adaptation needed. |

The source search for `perfect_hom_open_stage_maps` found only these two modules. The new
restriction-data module has no existing users. No module held by another group is adapted.
No target statement or definition used by a target changes. Local elaboration options do
not export a new notation, instance, or declaration to downstream signatures.

## Status

landed 20261013T224508-L-1470316 2026-10-13 (merge of deliver/F1/Sheaf.AlgebraicGeometry.PerfectHomOpenStageMaps)
