## What changed

Completed `MvPowerSeries.power_series_cohen_hypersurface_normality` in
`Sheaf.RingTheory.PowerSeriesCohenHypersurfaceNormality`, preserving its statement and the
DAG's five-step route. Added the proof import `Mathlib.RingTheory.MvPowerSeries.Inverse`
for the local-ring instance and the constant-coefficient unit criterion.

Three proved private helpers extract regularity from the existing field/Cohen theorem,
identify the Cohen maximal ideal using the existing constant-coefficient kernel theorem,
and transport normality from localization at the maximal ideal using
`IsLocalization.atUnits` and `IsIntegrallyClosed.of_equiv`.

The main proof sends the square of `(p, X)` into `(p)^2` by constant coefficient.
If the equation lay in that square, its constant coefficient would give `p^2 | p`;
cancellation of the nonzero uniformizer makes `p` a unit, a contradiction.
The existing regular-local hypersurface criterion then applies. The zero-variable
conclusions use `MvPowerSeries.isEmptyEquiv` and its induced quotient equivalence.
The argument uses no perfectness hypothesis. All existing proof-dependency modules
remain used, and no other existing module is changed.

Validation: the delivered Lean file compiled without warnings through `lcompile.py`
in 3.9 seconds, below the 60-second file limit.

## Proved and sorry left

Closed the one original hole:
`MvPowerSeries.power_series_cohen_hypersurface_normality`
(node `lem-trf-power-series-cohen-hypersurface-normality`).

Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
No decomposition or new unproved theorem is introduced. The proof uses the stated
regularity, quotient, localization, and normality declarations already in the library.

## No longer needed

None. No imports, nodes, or modules are pruned. Each planned dependency is used;
the blueprint unit route and the existing DAG proof remain applicable.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The existing field/Cohen regularity theorem packages
the Cohen prime existentially, so the proof recovers the maximal ideal for the given
prime directly from the kernel and unit criteria instead of identifying that witness.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
