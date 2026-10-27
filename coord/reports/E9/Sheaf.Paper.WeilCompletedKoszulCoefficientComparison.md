## What changed

Preserved the statement of
`AlgebraicGeometry.Scheme.completedKoszulCoefficientComparison` and replaced its
hole by composition of two comparisons through an explicitly constructed algebraic
ordered tensor of one-generator negative Koszul complexes. The composition includes
the consecutive transition square and the actual degree-zero unit equation, using
functoriality rather than an existence theorem for unspecified comparison data.

Added `WeilFiniteKoszulTensorModel` with real recursive definitions of this tensor,
its transitions and its degree-zero unit. Added `WeilExteriorKoszulTensorComparison`
with induction on the list length: its base case uses vanishing of positive exterior
powers of the zero module and the zeroth exterior equivalence; the induction step
uses only the first-generator splitting. Its transition proof uses the monoidal
composition identity; its unit proof checks the (0,0) summand.

Two distinct mathematical steps remain: the purely algebraic first-generator
splitting (`WeilKoszulAdjoinGenerator`) and coefficient/site transport of tensors
of rank-one negative factors to the internal dual of positive factors
(`WeilNegativeKoszulTensorDualTransport`). Each has one public theorem, its full
source argument in the docstring, and its own node. No source-library module,
existing definition, public import or theorem statement was changed.

## Proved and sorry left

Closed the existing hole in
`AlgebraicGeometry.Scheme.completedKoszulCoefficientComparison`
(node `lem-weil-pbc-completed-koszul-coefficient-comparison`).

Proved the new algebraic induction theorem
`AlgebraicGeometry.Scheme.exteriorNegativeKoszulTensorComparison`
(node `lem-weil-pbc-exterior-negative-koszul-tensor`), including the empty-list
identification, transition compatibility and unit compatibility.

Added two holes, both named public theorems in separate modules:

- `AlgebraicGeometry.Scheme.koszulAdjoinGenerator`
  (`lem-weil-pbc-koszul-adjoin-generator`): split off just the first generator over A,
  with no scheme, sheafification, completed scalar extension or internal dual.
- `AlgebraicGeometry.Scheme.negativeKoszulTensorDualTransport`
  (`lem-weil-pbc-negative-koszul-tensor-dual-transport`): transport the explicit tensor
  of rank-one factors, with no exterior-to-tensor comparison for a general list.

This is a decomposition: 1 original hole closed, 2 added, 2 remaining in the delivered
files. No net hole reduction is claimed. All four definitions in the intermediate
model are explicit; no data are chosen from an unproved existence theorem.

## No longer needed

No existing imports were removed. The original proof's three construction nodes
remain needed through the new lemmas: `def-weil-pbc-intrinsic-completion`,
`def-weil-pbc-ringed-koszul-system`, and
`def-weil-pbc-completed-cech-site-transport`. None of their modules is pruned.

The original direct ordered-subset comparison across all four coefficient/site
operations is replaced by the algebraic first-generator induction and separate
rank-one tensor dual transport. There is no need to add a second exterior basis,
a new Hom complex, a new derived comparison, a regular-sequence hypothesis, or a
Noetherian/ideal-generation argument. The unit route in
`dag/units/sk-thm-properbasechange.json` is preserved.

## Where the brief, the DAG or earlier work was wrong

The listed proof dependencies define the two Koszul models and their transports;
they do not state an isomorphism connecting them. Reading their actual declarations
and searching Mathlib and the source library found no direct theorem. The new
lemmas isolate the two missing calculations instead of treating them as implicit
consequences of the definitions. Stacks Tag 0664 explicitly omits its proof and
suggests the exterior-generator argument; that argument is spelled out here.

Checked the mathematical edge cases against the constructions: the empty list
uses A[0] and Hom(O[0],O[0]); rank one has positive Hom-dual differential
-(-1)^(-1)=+1; exterior and tensor transitions both multiply a subset by its
generator product. No cancellation is used, so zero and unit generators and the
zero ring are allowed. Finite basis constructions survive sheafification on an
empty site. No change to a target statement or its definitions is proposed.

## New nodes

`def-weil-pbc-finite-negative-koszul-tensor` records the four explicit algebraic
constructions in `Sheaf.Paper.WeilFiniteKoszulTensorModel`.

`lem-weil-pbc-koszul-adjoin-generator` records the first-generator splitting of
Stacks Tag 0664, including diagonal transitions and the empty-subset unit.

`lem-weil-pbc-exterior-negative-koszul-tensor` records the proved induction from
that local splitting to the ordered tensor of rank-one factors.

`lem-weil-pbc-negative-koszul-tensor-dual-transport` records the rank-one finite-free
dual and scalar/site transport calculation in Stacks Tag 0A0E. This uses only
one-generator exterior complexes, not the preceding comparison theorem.

The existing item's proof and proof dependencies now record composition through
these comparisons. No change record is required: all existing statements,
definitions and public imports are preserved.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
