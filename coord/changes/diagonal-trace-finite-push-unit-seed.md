# Common-unit pre-varying split

## Reason

The completed exact-square and coefficient-cone calculation is a separate pre-varying
morphism equality. Keeping it as a named theorem makes the seed proof a genuine
categorical transport argument through the varying isomorphism.

## Old

The item had one target theorem with a direct proof hole and no pre-varying theorem.
The exploratory direct expansion also used a proof-only coefficient-projection import.

## New

Added `Sheaf.Paper.DiagonalTraceFinitePushUnitCommon` with the pre-varying comparison
statement and imported it privately from `Sheaf.Paper.DiagonalTraceFinitePushUnitSeed`.
The seed theorem is proved by composing that comparison with the varying isomorphism
and simplifying inverse followed by hom. The pre-varying theorem remains the one
split proof obligation.

## Users

Only `Sheaf.Paper.DiagonalTraceFinitePushUnitSeed` imports the new module in this
delivery. No existing declaration or signature was changed.

## Status

Open split: the target theorem is proved; the pre-varying comparison is left for a
later worker under its new DAG node.
