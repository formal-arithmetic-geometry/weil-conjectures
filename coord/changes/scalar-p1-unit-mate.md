## Reason

The target proof needs six smaller categorical and trace interfaces plus one
shared instance cache. These additions make the target compile within the
per-file limit while preserving its statement.

## Old

The assigned module contained a large private calculation scaffold and a direct
trace equality conversion that exceeded the kernel time budget.

## New

The scaffold is replaced by six named intermediate theorem modules and the
`DerivedCalculationInstances` setup module. The target wrapper applies the
component assembly theorem to the packaged trace witness.

## Users

`Sheaf.Paper.ScalarP1UnitMateComponent` imports the new modules. Its public
theorem signature is unchanged; the additive declarations are consumed only by
this proof route.

## Status

landed 20261028T020141-L-2471562 2026-10-28 (merge of deliver/A5/Sheaf.Paper.ScalarP1UnitMateComponent)
for independent proof workers.
