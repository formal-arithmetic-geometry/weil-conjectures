## What changed

Restored `Sheaf.Paper.FiniteComparisonLocalizing` from its quarantine archive and
proved `finiteComparisonRealization_exact` using the internal module sheafification
 equivalence and the finite discrete ring transport. Added the proved helper module
`Sheaf.Paper.FiniteComparisonFaithful`, which cancels the exact coefficient realization
from the unbounded comparison to obtain ordinary full faithfulness. Added the localizing
closure inverse-image and essential-image argument and proved the assigned
`finiteComparisonLocalizing` theorem from that argument and the generator interface.
The generator-identification result is retained as a separate named split theorem.

Change record: `coord/changes/finite-comparison-localizing-proof-route.md`.

The final sandbox compiles with `lcompile.py --all` (both modules, exit code 0).

## Proved and sorry left

Holes closed: `finiteComparisonRealization_exact` and `finiteComparisonLocalizing`
(2 of 2 original holes).

A single strictly intermediate result is split off:
`finiteComparisonGenerators_identification` in
`Sheaf.Paper.FiniteComparisonLocalizing`, with node
`lem-ctf-finite-comparison-generators`. Its proof is the finite Noetherian coefficient
comparison transported through the constant-scalar and site equivalences; it is the
only `sorry` left. The helper `finiteComparisonOrdinary_fullyFaithful` is fully proved
in `Sheaf.Paper.FiniteComparisonFaithful`, with node
`lem-ctf-finite-comparison-ordinary-fully-faithful`.

## No longer needed

No imports, nodes, or modules are pruned. The existing operation and coefficient
imports remain needed by the definitions and the ambient comparison clauses.

## Where the brief, the DAG or earlier work was wrong

The assigned module was quarantined by the upstream-sync rework entry despite having
an active finite-comparison DAG route. The archived module's two holes were genuine
proof obligations; the coefficient exactness proof can be completed directly from the
internal module equivalence. The generator identification is a separate bounded
finite-Tor comparison result and is therefore split into its own named node rather than
repeating the localizing theorem under another name.

## New nodes

`lem-ctf-finite-comparison-ordinary-fully-faithful` records the proved helper module
`Sheaf.Paper.FiniteComparisonFaithful`.

`lem-ctf-finite-comparison-generators` records the split theorem
`finiteComparisonGenerators_identification`; its node is in the same chapter and uses
the existing finite-Tor comparison dependency.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
