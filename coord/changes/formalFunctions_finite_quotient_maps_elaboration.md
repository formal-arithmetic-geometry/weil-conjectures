# AlgebraicGeometry.formalFunctions_finite_quotient_maps

## Reason

The delivery preflight treats the added local irreducibility annotation as a module
command change and requires this record. The annotation prevents equality matching
from unfolding moduleCohomologyFMap into its chosen resolutions. Without it the final
composition repeatedly timed out at 60 seconds; with it the module compiles in about
25 seconds. The annotation is local to the item's section and does not alter the
underlying definition, its public reducibility, any theorem statement or any importer.
No target definition or target statement is changed; no target meaning review is
reopened. There is no forced adaptation.

## Old

The section previously began, verbatim:

```lean
namespace AlgebraicGeometry
noncomputable section
```

No local irreducibility annotation for moduleCohomologyFMap was present. The theorem's
original signature is retained verbatim in the delivery.

## New

The section now begins:

```lean
namespace AlgebraicGeometry
noncomputable section

-- Compare cohomology h-maps by their interfaces, without unfolding chosen resolutions.
attribute [local irreducible] Scheme.Modules.moduleCohomologyFMap
```

The existing theorem additionally has scoped elaboration and linter options, confined
to that one declaration. The heartbeat limit is 400000; backward transparency options
are false. The unused-variable linter is disabled for the unchanged coherent hypothesis,
which this formal compatibility argument does not use. These are proof elaboration
settings. The original public import and every existing signature/visibility stay
identical. Only non-public proof imports are removed or added.

## Users

`tools/downstream.py` finds 229 downstream modules, but its `--uses` result finds the
following two textual mentions of the theorem. There is one direct importer,
FormalFunctionsFiniteQuotientComparison. None needs adaptation: the annotation is
local, no public instance/attribute is added, and the theorem's type is unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientMaps | X3 | Proof elaboration only; declaration type unchanged. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientComparison | unclaimed | No exported interface change; existing application of the theorem remains valid. |

All other downstream modules inherit the same exported interface and need no changes.
No module held by another group is edited.

## Status

landed 20261013T062536-L-736941 2026-10-13 (merge of deliver/X3/Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientMaps)
