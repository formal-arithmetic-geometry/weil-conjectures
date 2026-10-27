## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.finitePerfectAdicOrdinaryCoefficient_comparison`.
The statement and its existing degreewise complex consequence are unchanged.
All added constructions and lemmas are private and proved in the item module.

The proof reuses the normalized completion-ring and finite-quotient comparisons
from `Sheaf.Paper.CompletedKoszulFiniteQuotientComparison`. Flatness gives
exactness of completed scalar extension. Normalization of the finite reduction
identifies the image of the quotient projection with the prescribed coefficient
projection; cancellation of that epimorphism gives naturality for every tower
map. The tensor comparison combines the explicit ULift tensor equivalence,
constant-sheaf monoidality transported through scalar restriction, and ordinary
scalar-extension tensor coherence. Two applications of `NatIso.ofComponents`
assemble the comparison, natural in both the module and coefficient index.

Proof imports were added for those existing results and Mathlib's tensor-product
ULift equivalence. The item's DAG proof and proof dependencies record this route.
No shared statement, definition, instance, public import, or other module changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.finitePerfectAdicOrdinaryCoefficient_comparison`
(node `lem-weil-pbc-finite-perfect-adic-ordinary-coefficient-comparison`).
The existing theorem
`AlgebraicGeometry.Scheme.finitePerfectAdicTensorComplexDiagram_ordinaryComparison`
still follows from it. Zero holes added; zero holes remain in the delivered module.
This is a proof from existing project declarations, with no split-off obligation.

## No longer needed

No existing public imports or modules are withdrawn. The four original planned
mathematical dependencies remain necessary, either directly or through the
normalized completion and quotient helpers reused from
`CompletedKoszulFiniteQuotientComparison`. The explicit local pure-tensor
construction is supplied by the existing scalar-extension and constant-sheaf
monoidal comparisons; no new lemma is needed for it.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The existing normalized ordinary quotient comparison
in `CompletedKoszulFiniteQuotientComparison` supplies the finite-reduction step;
it does not require reproving the complex comparison in that module. The DAG now
records this reuse and the scalar-restriction tensor equivalence used to identify
the ordinary ringed constant realization with fixed-coefficient constant sheaves.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
