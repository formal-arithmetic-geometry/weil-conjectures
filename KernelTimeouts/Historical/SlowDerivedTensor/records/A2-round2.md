# A2 round two

With the same bodies changed to `@[reducible] def`, the fresh tensor probe measured
`Kernel.check(value)` 1 ms and final conversion 46,358/51,680 ms forward/reverse.
The full consumer's final conversion was 2/2 ms, with a 1 ms value check. The exact
declaration hints were printed by `probes/round2/A1.lean`.
