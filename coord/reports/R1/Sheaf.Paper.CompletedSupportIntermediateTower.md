## What changed

In Sheaf.Paper.CompletedSupportIntermediateTower, prove ordinaryOpenInverse_isIso
and endpointInsertions without changing their statements or any definition.
A private proof import of StrictTowerProperOpenArrows exposes the existing
moduleOpenSquare, fixedOpen and exact-unit transport helpers. A proved private
openAdjunction_unit_isIso helper transports full faithfulness of extension by zero
through fixed-coefficient sheaves and exact derivation. The specified ordinary
open mate is a composite of isomorphisms: the open unit, the inverse pullback
square, and the open counit on an object in the extension functor's essential image.
Thus its unit normalization is retained, including for an empty open.

For endpointInsertions, transport invertibility through natural reconstruction
isomorphisms. Source pullback reconstruction uses reductionPullIso; target compact
support reconstruction uses mu and completionUnits. Both reduce to invertibility
of reduction applied to the completion unit, supplied by strictUnits.

## Proved and sorry left

Closed two existing holes, both in the namespace
AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower:
ordinaryOpenInverse_isIso and endpointInsertions. Added zero holes and zero
split-off statements. Seven holes remain in this module, all attached to
lem-cbc-completed-support-intermediate-tower:

- strictUnits
- completionUnits
- reconstructionNormalization
- exchangeSubstitution
- finiteUnits
- twoSubstitutions
- strictFiniteCoherence

The current shared baseline has nine holes. An X8 delivery landed seven other
proofs while this worker was preparing overlapping work; this packet starts from
that updated baseline and does not claim those seven closures.

## No longer needed

None. No imports, nodes or modules are withdrawn. The completed-support unit route
and all remaining stated dependencies are retained. No new public import is added.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The shared source advanced during the
session; the packet was rebased by copying the updated module before writing the
two proofs reported above. The ordinary open-base-change argument needs only the
existing module-level base-change isomorphism to identify the essential image;
it does not require asserting that an arbitrary mate of an isomorphism is invertible.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
