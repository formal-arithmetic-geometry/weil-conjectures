## What changed

Closed `section_tensor_transport` by assembling two strictly smaller transport
components.  The first component supplies a barB satisfying the complete
`SectionTensorNormalized` equations.  The second proves the
`TensorSectionCondition` for any such normalized barB.  The main module imports
these two split modules and combines their conclusions directly.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_tensor_transport` is
closed.  Two genuine lower-level holes remain:

* `AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_tensor_transport_normalized`
  (ordinary balancing, signed totalization, and section counit normalization);
* `AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_tensor_transport_condition`
  (conjugation of the supplied internal tensorator through the normalized section
  comparison).

Thus 1 of 1 original sorries is closed and 2 are split off.

## No longer needed

None.  The original proof dependencies remain needed by the two split components.

## Where the brief, the DAG or earlier work was wrong

The one-step DAG proof hides two independent non-elementary arguments: constructing
the normalized section tensor comparison and proving its conjugation with the given
internal tensorator.  They are now explicit statement nodes with the same source
route, while the parent theorem is a complete Lean assembly of those components.

## New nodes

* `lem-sfb-quotient-section-tensor-transport-normalized` owns
  `section_tensor_transport_normalized`.
* `lem-sfb-quotient-section-tensor-transport-condition` owns
  `section_tensor_transport_condition`.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
