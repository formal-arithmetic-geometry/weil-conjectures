# exists_properDerivedDirectImageComposition

## Reason

The proof needs additional heartbeats to elaborate the dependent comparison witnesses.
A proof-local option does not cover declaration elaboration, so maxHeartbeats is scoped
to this theorem as a command. The static stage-3 checker classifies any added command as
an interface change and requires this record. No statement, definition or instance changes.
The setting is scoped: it changes no compiler option for importers or other declarations.

## Old

The declaration had no scoped heartbeat setting (default 200000).
Its signature is unchanged, verbatim from the original module.

## New

`set_option maxHeartbeats 800000 in` applies only to the existing theorem declaration.
Its signature is unchanged. The proof reduces it to named composition, preservation,
unit-law and associativity statements. The file still compiles within the 60-second limit.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProperDerivedDirectImageComposition | A3 | Only elaboration budget and proof body change; statement unchanged. |

`tools/downstream.py Sheaf.AlgebraicGeometry.ProperDerivedDirectImageComposition
--uses exists_properDerivedDirectImageComposition` listed no users of the declaration.
All modules importing this file retain the same public declarations, definitions and
instances. No target's meaning changes.

## Status

landed 20261012T070526-L-3465684 2026-10-12 (merge of deliver/A3/Sheaf.AlgebraicGeometry.ProperDerivedDirectImageComposition)
