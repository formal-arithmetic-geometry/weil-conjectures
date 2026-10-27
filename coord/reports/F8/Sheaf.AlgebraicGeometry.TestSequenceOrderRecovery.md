## What changed

Replaced the sole `sorry` of
`AlgebraicGeometry.HilbertSamuel.test_sequence_order_recovery` by a complete Lean proof
assembling point-order and boundary-order recovery. The original signature, hypotheses,
universe and public imports are unchanged. Only the item, four new Sheaf modules and their
DAG records are delivered; no shared definition or other existing module is changed.

`TestSequencePointOrderRecovery` proves the numerical part of original step 7. It extracts
order >= mark from cosupport using injectivity of the closed embedding, then proves normalized
extended-natural order equality from the common divisor thresholds. The proof separates
finite/infinite cases. In the finite case a strict inequality `n*d < m*b` is separated by
`k=d*b`, `i=n*d-d*b`, avoiding real suprema, floors, and rational approximation. The reverse
inequality is excluded symmetrically. The three private helpers are fully proved.

`TestSequenceBoundaryOrderRecovery` proves original step 10: apply the proved point-order
result to two actual common test sequences with consecutive anisotropic weights, cast their
finite orders to natural numbers, and cancel the constant terms with `nlinarith`. Infinite
and zero boundary orders are handled separately. It does not subtract infinite orders.

The two remaining geometric constructions are separated into `CylinderTestThresholds`
(original steps 1--6 and the prefix part of 11) and `BoundaryOrderTestWitnesses` (original
steps 8--9 and the construction part of 10--11). The second statement records actual common
sequences, unchanged marks, paired ambient points, common cosupport membership, and finite
point-order formulas. It asserts no normalized boundary-order equality. Thus these are the
geometric parts of the argument, not a renamed copy of the original conjunction.

Source reading: opened the publisher's BM paper at
https://ems.press/content/serial-article-files/41043, especially Theorems 6.1 and 6.2,
printed pp.631--633. The paper's successful-pair construction and its two-successive-weight
argument agree with the retained plan. The nonclosed-point and arbitrary-common-prefix
extensions remain the agent refinement recorded by the existing DAG. No claim is made that
BM prints those additional formalization details verbatim. The new nodes use agent proof
provenance and retain the existing lower geometric dependencies.

Validation: `lcompile.py --all` compiled all five files cleanly, in import order. Latest times:
CylinderTestThresholds 2.9 s; TestSequencePointOrderRecovery 5.5 s;
BoundaryOrderTestWitnesses 3.4 s; TestSequenceBoundaryOrderRecovery 4.5 s;
TestSequenceOrderRecovery 3.0 s. Delivery runs the additional axiom and mechanical probes.
Every Lean line is at most 100 characters. Searches used LeanSearch, LeanFinder/Loogle,
Mathlib grep, both library roots and the DAG; no recovery or test-witness theorem was found.
The exact queries and returned candidates are recorded in the new nodes. Blueprint searches
for cylinder and boundary order returned no matching blueprint node. The unit's `realized`
fields are empty, and no unit or chapter route is changed.

Edge cases checked: unequal positive marks; finite order exactly the mark (empty successful
pair set); both orders infinite; either finite/infinite mismatch (excluded in the proved
arithmetic); empty boundary; a component missing the point even for a zero ideal; zero normal
dimension; disconnected supports; arbitrary nonclosed points; and intervening open steps.
The witness theorem has separate infinity and zero branches so it never demands finite
point-order witnesses for a missing component with zero ideal.

## Proved and sorry left

Closed the one original textual hole in
`AlgebraicGeometry.HilbertSamuel.test_sequence_order_recovery`
(node `lem-trf-test-sequence-order-recovery`), by a complete proof from the new geometric
reductions. This is a decomposition: 1 original hole closed, 2 lower holes added, net -1;
zero of the original holes is discharged without a remaining new geometric assumption.

Fully written proofs of the new intermediate declarations:

- `AlgebraicGeometry.HilbertSamuel.test_sequence_point_order_recovery`
  (`lem-trf-test-sequence-point-order-recovery`), including its finite/infinite arithmetic.
- `AlgebraicGeometry.HilbertSamuel.test_sequence_boundary_order_recovery`
  (`lem-trf-test-sequence-boundary-order-recovery`), including two-test slope cancellation.

Exactly two direct `sorry` proofs remain in this delivery, each in its own new module:

- `AlgebraicGeometry.HilbertSamuel.cylinder_test_thresholds`
  (`lem-trf-cylinder-test-thresholds`), common geometric divisor-test thresholds.
- `AlgebraicGeometry.HilbertSamuel.boundary_order_test_witnesses`
  (`lem-trf-boundary-order-test-witnesses`), two actual anisotropic test witnesses and
  the zero/infinite cases.

There is no `sorry` in a definition or private theorem, and none remains in the assigned
module. The two postponed theorems have source citations and complete proofs in words in
their declaration docstrings and matching nodes.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.MarkedControlledBlowupCharts`
- `Sheaf.AlgebraicGeometry.PermissibleCoordinateChart`
- `WeilConjectures.AlgebraicGeometry.Regular`
- `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`
- `Mathlib.RingTheory.KrullDimension.Regular`
- `Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula`
- `Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg`

Their geometric declarations remain needed below the new geometric nodes; this is removal
from the assembly proof, not withdrawal or whole-project pruning of those modules. Replaced
them by private proof imports of TestSequencePointOrderRecovery and
TestSequenceBoundaryOrderRecovery. The new point arithmetic and boundary cancellation use
private Mathlib tactic imports.

The declared dependencies `lem-trf-logarithmic-differential-transform` and
`lem-sc-lft-over-field-jacobson-space` are not needed on this proof route: RestrictedEquivalent
already asserts equality of cosupports at depth zero and passes it along every common finite
prefix. Recovering equality a second time from closed points is unnecessary. This does not
claim those nodes are globally unreachable or withdraw their declarations. Every other
original geometric proof dependency remains on the new nodes' proof routes.

Removed all six original top-level `tool_uses` entries from the item's assembly node:
lem-sc-lft-over-field-jacobson-space, lem-weil-pbc-smooth-scheme-over-field-regular,
lem-sc-regular-local-domain, lem-weil-pbc-dimension-quotient-nonzerodivisor,
lem-kun-dimension-formula, lem-sc-closed-irreducible-dimension-trdeg. Except for Jacobson
space they remain lower geometric tools, declared in the new nodes' proof plans for review.
No existing module is withdrawn; no definition is pruned. No new-node public import of
MarkedBoundaryOrder is needed in the point-order and cylinder modules.

## Where the brief, the DAG or earlier work was wrong

The previous source module imported seven geometric proof modules while its whole proof was
still `sorry`; these imports did not implement the plan. This delivery supplies actual Lean
arithmetic and combination proofs, and isolates the remaining geometric glue explicitly.

Original step 1 recovers cosupport equality by semicontinuity and Jacobson density, but the
landed definition of RestrictedEquivalent already includes it. Original step 7's real
supremum/floor argument can be replaced by the exact natural separation argument above.
Neither observation changes the theorem's mathematical statement.

The generic-center formal-normal-slice declaration has additional integral-component and
injective-label hypotheses. The remaining geometric nodes must obtain its locally relevant
version by shrinking/splitting smooth boundary components; the original point/boundary
statement cannot apply that declaration verbatim. The proof notes make this local adjustment
explicit rather than adding those hypotheses to the recovery theorem.

No false target, definition repair, or unit-route change is asserted. There is no independent
second reader in this worker session, as instructed; the delivery's independent review is
still required.

## New nodes

`lem-trf-cylinder-test-thresholds`: the common cylinder divisor-test comparison, with its
own module CylinderTestThresholds and one postponed proof. It contains original geometric
steps 1--6 and the prefix invariants of 11, without the numeric separation argument.

`lem-trf-test-sequence-point-order-recovery`: proved normalized point-order recovery from
those thresholds; the finite/infinite numerical argument is in Lean, not a new hole.

`lem-trf-boundary-order-test-witnesses`: actual paired test sequences at two consecutive
anisotropic weights, plus separate common-zero and common-infinite boundary cases. Its one
postponed proof contains the geometric constructions of steps 8--11 and uses point recovery.

`lem-trf-test-sequence-boundary-order-recovery`: proved application of point recovery to the
two witnesses and finite slope cancellation. No new shared definitions or change record are
needed, since existing signatures, public imports, definitions and other modules are unchanged.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
