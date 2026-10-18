## What changed

Proved `FiniteField.exists_unique_subfield_of_closure` in
`Sheaf.FieldTheory.UniqueSubfieldOfClosure`, preserving its statement and existing public
imports. Added the proof-only import `Mathlib.Algebra.CharP.CharAndCard` to obtain the
characteristic from the prime-power cardinality.

The proof follows the six-step DAG plan. It constructs the subfield as the equalizer of
the nth Frobenius automorphism and the identity. `Polynomial.card_rootSet_eq_natDegree`
packages the splitting and separability argument for its cardinality. Any subfield of
the required cardinality lies inside this equalizer by `FiniteField.pow_card`, and finite
cardinality proves equality. Degree one identifies the base-field image; the iterated
power equation proves containment, and corestriction supplies the ring homomorphism.

## Proved and sorry left

Closed 1 hole: `FiniteField.exists_unique_subfield_of_closure`
(node `lem-weil-unique-subfield-of-closure`). Added 0 holes; 0 sorries remain in the item.
No intermediate obligations were split off. Single-file compilation passed without
diagnostics. The declaration's axioms were checked separately with `#print axioms`.

## No longer needed

None. No imports, nodes or modules are pruned. All declared mathematical dependencies
remain represented by their existing Mathlib declarations. The factorization and simple-root
inputs are combined through Mathlib's root-set cardinality theorem, without new Sheaf imports.
The unit route is preserved and the node's proof and dependencies are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. `IsAlgClosure.isAlgClosed` must be installed explicitly
as a local instance; the existing algebraicity instance already supplies the Frobenius
construction. This is an elaboration detail, with no statement or definition repair.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
