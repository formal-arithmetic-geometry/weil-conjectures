# Retire the equivariant sheaf compatibility interface

## Reason

Complete upstream review #1428's duplicate removal by pointing every remaining
caller directly to the single retained implementation. The previously landed
repair removed the duplicate proof but left a public-import compatibility module
in the target closure. Retire its re-export and re-point its two direct importers.
Keep the empty historical file; pruning removes it from the targets' import closure.
No theorem, definition, target signature, or unit route changes.

Repair of the broken tip 5bf94fe6cda6b904f1042bf7e0efe2a2724a39b7:
removing every import also removed command elaboration from the public environment.
The global build's importing axiom/sorry probe then failed with
`unknown namespace Command` and `include import Lean.Elab.Command`.
Keep a public infrastructure import of `Mathlib.Init`, which exports the command
elaborator and axiom inspection API without restoring the mathematical re-export.

## Old

In `Sheaf.ConstructibleSheaf.TorsorEquivariantPresheafSheaf`:

```lean
public import Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf
```

This re-export supplied
`AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf`
to the two modules below through the historical import path.

## New

`Sheaf.ConstructibleSheaf.TorsorEquivariantPresheafSheaf` has no declarations or
mathematical imports. Its only import is the infrastructure needed by the probe:

```lean
public import Mathlib.Init
```

The existing module docstring is preserved verbatim; its historical description
of having no imports predates this infrastructure repair.
In each caller the landed replacement of the historical proof import remains:

```lean
import Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf
```

The retained theorem and all caller signatures, visibilities, definitions, and
proof bodies are unchanged. The DAG already names the retained theorem's module;
no node edit is needed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.ConstructibleSheaf.TorsorInvariantSections | unclaimed | Forced import replacement at line 9; the original fails at line 78 with lean.invalidField for equivariantModulePresheaf_isSheaf. |
| Sheaf.ConstructibleSheaf.TorsorSectionEvaluationBijective | unclaimed | Forced import replacement at line 11; the original fails at line 69 with lean.invalidField for equivariantModulePresheaf_isSheaf. |

These are all direct importers of the retired module. The third theorem caller,
`Sheaf.ConstructibleSheaf.TorsorAssociatedModuleFull`, already directly imports
the canonical module and requires no adaptation.

## Status

landed 20261014T044553-L-1450952 2026-10-14 (merge of deliver/XRb0cc22400e136910/Sheaf.ConstructibleSheaf.TorsorEquivariantPresheafSheaf)

Previously landed 20261014T035544-L-887616 2026-10-14 (merge of deliver/M1/Sheaf.ConstructibleSheaf.TorsorEquivariantPresheafSheaf); this repair is the independent-reader follow-up.

