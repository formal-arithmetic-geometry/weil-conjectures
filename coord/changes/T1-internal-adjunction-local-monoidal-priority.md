# Sheaf.SmoothPurity.InternalAdjunctionEvaluation: local monoidal instance priority

## Reason

The proof uses the existing direct monoidal-localization instance. Previously the
proof-only import below supplied its high global priority. Removing that unused
mathematical dependency leaves the same preference installed locally in the item.
The static preflight classifies an added attribute command as an interface change
and requires this record even though the command is local.

No existing declaration signature, definition, visibility, or public import changes.
The new private lemmas are all proved. The local attribute ends with the namespace
and supplies no instance-priority change to an importing module. No target's
statement or any definition it uses changes, so no target review is reopened.

## Old

The item had this proof-only import, verbatim:

```lean
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
```

That imported module contains this priority command, verbatim:

```lean
attribute [instance high] GrothendieckTopology.W.monoidal
```

There was no local priority command in the item.

## New

The proof-only import is removed. Inside `namespace AlgebraicGeometry.Etale`, the
item now contains:

```lean
attribute [local instance high] GrothendieckTopology.W.monoidal
```

The preference is local to elaborating this file. The theorem's complete original
signature, its canonical maps, and all public imports remain verbatim.

## Users

`tools/downstream.py Sheaf.SmoothPurity.InternalAdjunctionEvaluation --uses
internalAdjunctionEvaluation` found the four downstream modules below, and no
consumer mentions the theorem name. All direct importers and the sole transitive
importer are listed; no consumer adaptation is needed because the declaration
interface is unchanged and the priority command is local. The current claim
snapshot records S7 for DeltaProperPushforward and no holder for the other three
consumer modules. No module held by another group is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SmoothPurity.InternalAdjunctionEvaluation | T1 | Proof completed; same public interface; priority preference local. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | Direct proof import; statements and available public declarations unchanged. |
| Sheaf.Paper.DeltaProperPushforward | S7 | Direct proof import; statements and available public declarations unchanged. |
| Sheaf.Paper.FiniteExceptionalInternalHom | unclaimed | Direct public import; no signature, definition, or public import removed. |
| Sheaf.Paper.DualizingLocallyClosedInheritance | unclaimed | Transitive consumer through FiniteExceptionalInternalHom; public interface unchanged. |

## Status

landed 20261020T174849-L-811828 2026-10-20 (merge of deliver/T1/Sheaf.SmoothPurity.InternalAdjunctionEvaluation)
