# Shared counit trace control

The valid prefix ending after `scalarCounit_natural` was run with `trace.Meta.isDefEq`, `trace.profiler`, and high diagnostics thresholds. The trace emitted many tiny instance-oriented comparisons (including `Field`, `Algebra`, and `Semiring` paths) rather than a single slow conversion; a full trace exceeded the bounded run. This is negative evidence against assigning a specific Meta mechanism, not evidence that the comparisons are cheap in aggregate.

