# Sheaf.Paper.CompletedPullbackTowerRealizations interface repair

## Reason

The returned delivery required the original async setting and exposed model bodies,
removal of the continuation-module restructuring, and a real adjacent transition square
before closing the strict tower existence/uniqueness theorem. The measured inline level
definition exceeded the per-file compiler limit, so that definition remains in its
separate public module.

## Old

The returned version used `Elab.async true`, local-alias bodies for the two exposed
model definitions, and a fixed-level naturality theorem. It also included continuation
modules and marker declarations.

## New

`Elab.async false` and the original direct model-composition bodies are restored. The
public level definition is still supplied by `CompletedPullbackTowerTensorLevel` because
its inline compile was measured above the limit. The new transition module states the
actual `n+1` to `n` square. `CompletedPullbackTowerIsoExistence` proves the strictly
simpler existence statement using `NatTrans.ofOpSequence` and `NatIso.ofComponents`; the
item theorem adds uniqueness by extensionality. The target signature is unchanged.

## Users

`Sheaf.Paper.CompletedPullbackTowerRealizations` direct importers continue to see the
public finite-level definition. The new proof-only imports add no public declarations to
those importers.

## Effect

The target sorry is closed, with one strictly simpler transition-square sorry split off.
The exposed definitions are definitionally unchanged from the returned base, and the
item compiles within the per-file limit.

## Status

landed 20261027T233820-L-4119141 2026-10-27 (merge of deliver/C2/Sheaf.Paper.CompletedPullbackTowerRealizations)
