# WeilConjectures.SfbHomFilteredColimit.RepresentativeAPI

## Reason

Expose the existing proved representative calculations through a small public interface.
The item can use their statements with an ordinary proof import, without importing all
private implementations from three large modules. No existing construction, signature,
attribute or public import changes.

## Old

The module `Sheaf.Paper.InternalHomRepresentativeAPI` and its namespace did not exist.
The calculations were private declarations in the strict-model data, finite-free-stage,
and filtered-continuity modules.

## New

The new module defines the actual sheafification-unit `pure` tensor and the canonical
`singleTensorIso`. It proves `tensorGenerator_hom`, `tensorGenerator_hom_ext`,
`homValue_map_right`, `tensorPreadditive`, `resolutionProperties`, `homFixedQuasiIso`,
`tensorLeft_finiteFree_exact` and `tensorLeft_colimit_exact` by the existing calculations.
Their exact Lean signatures and constructions are in the module; every proof is complete.
The new node is `lem-sfb-strict-representative-interface`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.InternalHomRepresentativeAPI | R3 (new) | Interface, no holes. |
| Sheaf.Paper.DerivedInternalHomFilteredColimit | R3 | Ordinary proof import; all 13 public signatures and all public definition bodies unchanged. |

There are no existing consumers of the new namespace. No forced adaptation is made,
and no adopted source-library module is changed. The new definitions do not occur in
any target statement.

## Status

landed 20261021T120511-L-3903832 2026-10-21 (merge of deliver/R3/Sheaf.Paper.DerivedInternalHomFilteredColimit)
