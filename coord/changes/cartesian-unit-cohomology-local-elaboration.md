# AlgebraicGeometry.Scheme.Modules.cartesian_unit_cohomology_pullback_comp

## Reason

The proof uses the named canonical sheafification and Ext instances for the three
schemes. Registering them locally in the module, rather than introducing six local
instance lets in the theorem, reduces elaboration of the nested cohomology comparisons.
The transparency option permits matching the existing scheme/module type synonyms.
The delivery checker conservatively classifies added attribute/option commands as a
visible change and therefore requires this record. Both settings are confined to this
module: the instances are explicitly local, and Lean options are not exported.
No existing declaration signature, public import, definition or mathematical statement
changes. No downstream adaptation is needed, and the challenge statements retain exactly
the same definitions and meaning.

## Old

The original elaboration header following the public imports was:

```lean
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
```

## New

```lean
@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
```

## Users

The downstream declaration search finds one caller besides the item. All 112 transitive
importers retain their original elaboration environment and exported declarations; the
local instances and option do not propagate across module boundaries.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Cohomology.CartesianUnitCohomologyPullbackComposition | C3 | Local proof elaboration only; signature unchanged. |
| Sheaf.AlgebraicGeometry.Curve.CartesianUnitCohomologyTransport | unclaimed | Calls the unchanged theorem; no adaptation or semantic change. |

## Status

landed 20261013T181054-L-2598405 2026-10-13 (merge of deliver/C3/Sheaf.AlgebraicGeometry.Cohomology.CartesianUnitCohomologyPullbackComposition)
