## What changed

Proved `Algebra.isReduced_tensorProduct_of_finiteSeparable` in
`Sheaf.FieldTheory.FiniteSeparableTensorFieldReduced`, preserving its signature.
Replaced the private proof import of
`Sheaf.RingTheory.SeparablePolynomialQuotientReduced` with
`Mathlib.RingTheory.Unramified.Field`. Separability gives formal unramifiedness;
base change preserves it; finite-dimensionality supplies essential finite type.
Mathlib then gives reducedness over the field E, and tensor commutativity
transports it to the stated factor order. Updated the proof docstring and the
existing DAG node's proof, proof dependencies, and proof origin accordingly.
All public imports are unchanged.

## Proved and sorry left

Closed the sole original hole:
`Algebra.isReduced_tensorProduct_of_finiteSeparable`
(node `lem-weil-pbc-finite-separable-tensor-field-reduced`).
Holes closed: 1. Holes added: 0. Sorries left in the delivery: none.
The server single-file compile passed; the axiom check uses only
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the proof import `Sheaf.RingTheory.SeparablePolynomialQuotientReduced`.
The following planned proof dependencies are unnecessary for this theorem:

- `lem-weil-pbc-finite-separable-extension-primitive-element`: no primitive element is chosen.
- `def-weil-polynomial-ring`: no explicit polynomial presentation is needed.
- `def-pc-separable-polynomial`: separability is consumed through Mathlib's unramified API.
- `lem-weil-pbc-simple-algebraic-extension-power-basis`: no power basis is constructed.
- `lem-weil-pbc-polynomial-scalar-extension`: no polynomial scalar extension is used.
- `lem-weil-pbc-tensor-quotient-base-change`: no quotient presentation is used.
- `lem-weil-pbc-separable-polynomial-quotient-reduced`, whose module is
  `Sheaf.RingTheory.SeparablePolynomialQuotientReduced`: reducedness follows
  directly from Mathlib's theorem for unramified algebras over fields.

These are removed from this node's proof dependencies only; declarations and
modules used elsewhere remain in the library. The separable-extension definition
remains a dependency. This node is below the unit's realized statement and steps;
none of the unit's statement, steps, or realized nodes is removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

The original polynomial argument is valid but unnecessarily long given the
existing Mathlib results. The node's own `mathlib_candidate` had already identified
the shorter formally unramified chain, which compiles directly. There is no
statement or definition repair, no new node, and no forced adaptation.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
