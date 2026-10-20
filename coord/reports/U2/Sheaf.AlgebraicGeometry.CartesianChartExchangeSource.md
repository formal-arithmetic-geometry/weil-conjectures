## What changed

Retired Sheaf.AlgebraicGeometry.CartesianChartExchangeSource in favor of the
already-proved official module
WeilConjectures.AlgebraicGeometry.CartesianChartExchangeSource, following the
assigned retirement row and the human's 2026-10-20 retirement instruction.

Changed exactly one line in its sole direct consumer,
Sheaf.AlgebraicGeometry.CartesianChartExchangeAdjunction: the private import all
now names the official twin. The three helper signatures and proofs match the
official module verbatim modulo whitespace. All consumer declarations and proofs
are preserved. No upstream file or target changes.

Change record: coord/changes/U2-retire-cartesian-chart-exchange-source.md.
Validation: all seven direct/transitive consumers compiled successfully through
lcompile.py in dependency order, using the changed consumer as an overlay.
The unchanged LiftRawNaturality and LiftNaturality sources emitted existing
style warnings (long lines and letI); they are not modified or delivered.
The import-direction and before/after closure checks passed.

## Proved and sorry left

This is a zero-hole duplicate-retirement repair. Initially 0 sorry holes;
closed 0, added 0, left 0; split off 0. The removed private lemmas
AlgebraicGeometry.Etale.natural_conjugate,
AlgebraicGeometry.Etale.square_single_naturality and
AlgebraicGeometry.Etale.square_single_source remain proved in the official
module with exactly the same statements and proofs. No declaration retains or
receives a sorry in this delivery.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.CartesianChartExchangeSource.
Removed its sole direct import from
Sheaf.AlgebraicGeometry.CartesianChartExchangeAdjunction, replacing it with
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeSource.
The duplicate's imports disappear with it; the official module retains the
same mathematical dependencies. No other module or mathematical dependency is
claimed to be pruned.

No DAG node, unit or chapter record mentions this module or its helper names;
no quarantined Lean file references the withdrawn module. No node attachment
or parent proof dependency needs changing. All seven consumer closures cease
to reach the withdrawn module, with no new twin pairs. The Source twin pair
already present in the three Lift consumer closures disappears.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a module with a sorry or repair; the current
queue specifically assigns retirement, and this source has zero holes. The
retirement authorization is coord/retire-items.tsv together with
coord/changes/retire-sheaf-twins-20261020.md. The module has no DAG attachment;
there is no mathematical statement or unit-route error to repair.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
