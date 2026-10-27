# CategoryTheory.StageSystem.faithful_hom_transport

## Reason

The theorem uses only StageSystem, stage Hom groups, and DirectedSystem. The supplied
exact and shift structures of ExactStagePairData are unnecessary. Remove its public
import while preserving the theorem signature and all remaining public imports.

## Old

```lean
public import Sheaf.CategoryTheory.ExactStagePairData
public import WeilConjectures.CategoryTheory.StageSystem.Preadditive
public import Mathlib.Order.DirectedInverseSystem
```

## New

```lean
public import WeilConjectures.CategoryTheory.StageSystem.Preadditive
public import Mathlib.Order.DirectedInverseSystem
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FaithfulStageHomTransport | F3 | The signature uses only the retained imports. |

A search of all Lean sources found no direct importer of this item module and no
external reference to faithful_hom_transport. No consumer needs adaptation. The
pending parent in the DAG needs only this theorem, whose signature is unchanged.
The definition dependency def-sf-directed-common-stage-data remains: its underlying
StageSystem and PairCategory are supplied by the retained Preadditive import.
No target statement or definition changes.

## Status

landed 20261027T094402-L-221127 2026-10-27 (merge of deliver/F3/Sheaf.CategoryTheory.FaithfulStageHomTransport)
