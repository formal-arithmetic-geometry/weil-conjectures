## What changed

Filled `AlgebraicGeometry.Scheme.pbcIsoRationalScalarComparison_comp` without changing its
statement or any public interface. The proof follows the recorded three-step route:
sectionwise restriction/direct-image compatibility and mates; complex-counit normalization
and uniqueness of the derived comparison, followed by the faithful integral inclusion;
and conjugation by the rational localization comparisons. All auxiliary results are proved
private helpers in the item module. Added a private proof import of the finite-stage module to use its normalization lemmas.
Local opacity and implicit-reducibility attributes control proof elaboration only.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.pbcIsoRationalScalarComparison_comp`
(node `lem-sf-pbc-rational-automorphism-coherence`). One original hole closed; zero new holes;
zero holes remain in the delivered module. No statements are split off.

## No longer needed

None. Both recorded dependencies, `def-wf-automorphism-completed-transport` and
`def-weil-pbc-finite-stage-pair-category`, are used. No imports, nodes, or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The existing statement, its repeated-field cases,
and the unit route are preserved.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
