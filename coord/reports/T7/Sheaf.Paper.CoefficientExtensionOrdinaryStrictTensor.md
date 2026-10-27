## What changed

Proved `WeilConjectures.coefficientExtensionOrdinaryStrictTensor_exists` in
`Sheaf.Paper.CoefficientExtensionOrdinaryStrictTensor`. The ordinary functor and
complex functor keep their original data. Mathlib’s degreewise isomorphism
constructor replaces the hand-built record with the same component maps. The
evaluation constructor folds
private definitional aliases; its data is definitionally equal to the original
constructor. The public statement and public imports are unchanged.

Proved private helpers identify finite inverse evaluations with the projection
model's tensor generators, and identify the actual coefficient transition with
horizontal restriction. The projection generator formula gives quotient reduction
on tensors. After forgetting to abelian sheaves, sheafification hom-extensionality
and tensor induction identify the conjugated transition with the published scalar
transition. Cancelling the evaluation isomorphisms gives the required formula on
all sections. Explicit equality transports keep the abelian comparison maps in
their native sheaf types. Generic heterogeneous equalities preserve the native section types
when scalar restriction changes their presentation.

The node records this argument. The private folding change and its consumer audit
are documented in `coord/changes/T7-ordinary-strict-tensor-private-evaluation-fold.md`.
No consumer needs adaptation.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.coefficientExtensionOrdinaryStrictTensor_exists`
(node `stage3-pur-extension-ordinary-strict-tensor`).

Holes closed: 1. Holes added: 0. Sorries remaining in the delivered module: 0.
No intermediate unproved theorem is introduced.

The complete module compiles through `lcompile.py` in 45.5 seconds with no
warnings or errors. The completed proof was also checked with `#print axioms`,
which reported only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

No dependency node or module is pruned. Both original proof dependencies remain
used, together with the coefficient sequence site's existing statement dependency.
No original import or declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The existing ordinary constructors and generator transition formulas suffice.
The final comparison can be made in abelian sheaves, preserving equality on every
section, including level zero and the empty scheme. No flatness, unramifiedness,
or nonzero-section hypothesis is added, and the unit route is preserved.

The historical source path in the node has moved in the current blueprint to
`literature/blueprint/latest/blueprint/sec-proetale-coefficients/` followed by
`sk-prop-sf-open-closed-triangle/def-weil-derived-pullback-tensor-hom.md`.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
