## What changed

Proved `Module.finitePresentation_iff_of_finite_of_finitePresentation` in
`Sheaf.RingTheory.FiniteExtensionModuleFinitePresentation`, with its signature,
docstring, and imports unchanged. The proof follows both existing DAG steps.
For the forward implication, finite module generation supplies algebra finite
type, and `Module.FinitePresentation.of_finiteType_subring` applies after
identifying its restricted module structure using
`IsScalarTower.algebraMap_smul`. For the reverse implication, Mathlib's
`Module.FinitePresentation.of_finite_of_finitePresentation` supplies finite
presentation of S over R, and `Module.FinitePresentation.trans` completes the
argument. No additional assumptions, declarations, nodes, or definition repairs.

## Proved and sorry left

Closed the one existing hole in
`Module.finitePresentation_iff_of_finite_of_finitePresentation`
(node `lem-trf-finite-extension-module-finite-presentation`): 1 of 1.
There are zero holes left in the item and zero holes added or split off.
The existing imported theorem
`Module.FinitePresentation.of_finiteType_subring`
(node `lem-trf-finitely-presented-over-subring`) remains an unproved dependency;
this delivery proves the assigned theorem from its stated dependencies.

## No longer needed

None. Every existing proof import is used, and all four declared proof
dependencies remain needed. The proof follows the existing DAG route, so no
node updates or module withdrawals are necessary.

## Where the brief, the DAG or earlier work was wrong

None. The scalar-tower hypothesis identifies the arbitrary given R-module
structure with restriction along the algebra map, so the ring-homomorphism
form of the stated forward-direction dependency applies without changing
any statement. The proof also permits the zero module and trivial rings;
no nontriviality or faithfulness assumptions were introduced.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
