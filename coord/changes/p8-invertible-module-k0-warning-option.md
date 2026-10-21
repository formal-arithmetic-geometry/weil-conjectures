# Module.FiniteProjectiveK0.class_of_finite_free_resolution

## Reason

Repair the returned delivery `33bd9a671`. The source hole ledger mistakes the
`sorry` component of the file-level warning option for an unattributed proof
hole. The option is unnecessary after proving the theorem. Remove it rather
than suppressing warnings. Preflight classifies this file-level command removal
as an interface change, so this record documents its exact extent.

## Old

```lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false
```

## New

```lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
```

Every existing declaration signature, visibility, and public import is identical.
The four new helpers are private proved theorems. The public theorem now has a
complete proof. No definition is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.InvertibleModuleK0Class | P8 | Remove a warning suppression; complete the existing theorem proof. |

`tools/downstream.py Sheaf.TraceFormula.InvertibleModuleK0Class --uses
class_of_finite_free_resolution` reports zero downstream modules on the current
source. A direct textual import search under both library roots also finds no
consumer. The earlier importer `Sheaf.RingTheory.RegularLocalPicardZero` has
independently stopped importing this module; this delivery does not change it.
Warning options are local to elaboration of their file, so their removal changes
no imported declaration or target meaning. No consumer adaptation is required.

## Status

landed 20261021T190559-L-3659409 2026-10-21 (merge of deliver/P8/Sheaf.TraceFormula.InvertibleModuleK0Class)
