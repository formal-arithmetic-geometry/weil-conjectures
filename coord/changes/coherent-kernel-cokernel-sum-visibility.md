# Sheaf.AlgebraicGeometry.CoherentKernelCokernelSum proof universes

## Reason

The delivery checker classifies changes to module commands as interface changes.
The only changed command in the existing module is the addition of the universe
names `v w`, used by two new private helpers for sheaves on a general site.
The existing public theorem still has only universe `u`, with its signature byte
for byte unchanged. The existing open commands and local finite-biproduct instance
attribute are unchanged; the previous version of this record incorrectly claimed
otherwise. No definition or theorem statement changes.

## Old

```lean
universe u
```

## New

```lean
universe u v w
```

## Users

The source-only downstream check found 704 downstream modules and five modules
mentioning the declaration, including this module. The universe names do not occur
in the public declaration; none of these users require any adaptation.
The four downstream declaration users and the item are listed below. There is no
changed statement or definition requiring an interface migration.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CoherentKernelCokernelSum | T1 | Private helper universes only. |
| Sheaf.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes | not needed for this proof-only command change | None. |
| Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian | not needed for this proof-only command change | None. |
| Sheaf.AlgebraicGeometry.CoherentSheafHom | not needed for this proof-only command change | None. |
| Sheaf.AlgebraicGeometry.PushforwardCoherentOnOpen | not needed for this proof-only command change | None. |

## Status

landed 20261012T211618-L-1058419 2026-10-12 (merge of deliver/T1/Sheaf.AlgebraicGeometry.CoherentKernelCokernelSum)
