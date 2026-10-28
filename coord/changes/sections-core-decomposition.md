# CoefficientDerivedSectionsCore decomposition

## Reason

The generic comparison declarations use strict semilinear systems, while the item uses
sequence-site modules. The proof is therefore exposed as two strictly smaller transport
interfaces before the final structure assembly.

## Old

`coefficientDerivedSectionsCore` was proved by `sorry`.

## New

`coefficientDerivedSectionsCore` assembles `CoefficientDerivedSectionsCoreData` and the
resolution/projection equations into the requested package.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.CoefficientDerivedSectionsNormalization` | unclaimed | imports the completed core theorem |

## Status

landed 20261028T020244-L-2485556 2026-10-28 (merge of deliver/D3/Sheaf.Paper.CoefficientDerivedSectionsCore)
