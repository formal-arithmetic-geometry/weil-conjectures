# Strict étale isomorphic-stage projection interfaces

## Reason

Move `StrictEtaleQuotientProjection`, its normalized `projection` composition, and
`StrictEtaleTransportProjection` into a small public interface module.  This lets the
coefficient transport construction and the compact-support mate assembly be stated in
separate modules without an import cycle.  Names, signatures, bodies, and visibility are
unchanged; the original target module publicly imports the interface module.

## Old

The three declarations were in
`lean/Sheaf/Paper/StrictEtaleIsomorphicStageProjection.lean`.

## New

The declarations are in
`lean/Sheaf/Paper/StrictEtaleIsomorphicStageProjectionInterfaces.lean`; the original module
publicly imports that file and retains the theorem
`AlgebraicGeometry.strictEtaleIsomorphicStageProjection`.

## Users

`Sheaf.Paper.EtaleCoefficientSystemAdjoint` is the only direct importer of the target module.
It continues to receive all three declarations through the target's public import.  The new
construction modules import the interface module directly.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | unclaimed | Existing import and names remain valid; no edit needed. |
| Sheaf.Paper.StrictEtaleIsomorphicStageProjection | G3 | Publicly reexports the moved declarations and proves the target theorem. |
| Sheaf.Paper.StrictEtaleIsomorphicStageProjectionInterfaces | G3 | New module containing the unchanged declarations. |

No source-library declaration or target statement changes.
