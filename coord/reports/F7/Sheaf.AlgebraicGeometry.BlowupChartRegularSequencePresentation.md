## What changed

Proved `AlgebraicGeometry.blowupChartRegularSequencePresentation` in
`Sheaf.AlgebraicGeometry.BlowupChartRegularSequencePresentation`, with its statement
unchanged. The proof follows the current four-step DAG assembly: specialize
`RingTheory.Sequence.polynomial_regular_sequence_syzygies` to `s + 1` entries and
`s` variables; convert its `Pi.single` vectors to scalar multiples of unit vectors;
apply `RingTheory.koszul_relations_quotient_torsionfree`; and use the kernel formula
and surjectivity from `AlgebraicGeometry.blowupChartPresentationPowerTorsion` to
construct `AlgEquiv.ofBijective`. The variable-image clause is inherited unchanged
from the chart map. All three proof dependencies are imported privately.

The proof compiled cleanly through `lcompile.py` in 3.1 seconds. It uses no
nonemptiness simplification or cancellation in the original ring. The empty
variable case `s = 0` is included by the same specialization (the sequence length
is still one), with no added hypotheses. The chosen chart map is determined by
its values on the quotient polynomial generators, rather than arbitrary data
chosen from a mere existence result.

Searches through `msearch.py` (Lean Finder, Loogle, grep) and local `rg` found no
shorter exact presentation theorem. The current node already records the proof
route actually used, so no DAG modification is needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.blowupChartRegularSequencePresentation`
(node `lem-trf-blowup-chart-regular-sequence-presentation`).

Zero `sorry` remain in the item module. Added zero holes and split off zero
statements. The proof uses the existing declared dependencies; their unfinished
proofs are not changed by this delivery.

## No longer needed

Removed direct private imports `WeilConjectures.AlgebraicGeometry.KoszulComplex`
and `WeilConjectures.RingTheory.RegularSequenceKoszulRegular`. Their low-degree
Koszul argument is encapsulated by the existing polynomial-syzygy theorem.
Those nodes and modules remain needed transitively by that dependency, so no
module or node is claimed as pruned. All current declared proof dependencies are
used, including the polynomial universal property through the chart-map lemma.
No public imports were changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical or tooling error was found. The module's original proof imports
predated the current DAG split, so the proof now imports the three existing
statement modules rather than developing their arguments again. The current DAG
and the unit route are preserved.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
