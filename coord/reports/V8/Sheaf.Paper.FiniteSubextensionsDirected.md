## What changed

Proved `PadicAlgCl.finiteSubextensions_directed` in
`Sheaf.Paper.FiniteSubextensionsDirected` without changing its statement or any definition.
The degree inequality is an induction on the finite index cardinality using Mathlib's
`IntermediateField.finrank_sup_le`; the successor supremum equality is proved by its two
lattice inequalities. Finiteness uses the existing finite-supremum instance, and inclusion
uses `le_iSup`. The bottom-field instance gives nonemptiness and binary suprema give
common upper bounds. A finite subset is contained in its actual intermediate-field
adjunction, finite by `IntermediateField.finiteDimensional_adjoin`; singleton containment
then proves the final union assertion.

Updated the existing node's proof, proof dependencies and proof origin to record this route.
Removed the proof-only import `Mathlib.LinearAlgebra.Dimension.Free`.

Searches through the required msearch wrapper: LeanFinder for the compositum degree bound
and finite algebraic adjunction, Loogle for `IntermediateField.finrank_sup_le`, and grep for
`finrank_sup_le|finiteDimensional_adjoin|iSup_univ_succ|prod_univ_succ`. The first two returned
exact component matches; the finite-family induction remains an explicit Lean argument.
Also searched both project library roots for existing proofs of these components.

## Proved and sorry left

Closed the one original hole: `PadicAlgCl.finiteSubextensions_directed`
(node `det-def-sfb-qlbar-condensed-subextensions`). All five conjuncts are proved.
Added zero holes; zero sorries remain in the delivered module. No split-off declarations.
The empty finite family is handled explicitly by the degree-one bottom field. The finite
adjunction argument includes the empty subset. No arbitrary witness is chosen from an
unproved theorem.

## No longer needed

Removed import: `Mathlib.LinearAlgebra.Dimension.Free`.

The proof no longer needs node `lem-weil-pbc-compositum-degree-bound` (its relative-degree
bound) or node `lem-weil-pbc-field-degree-multiplicativity` (the tower law). Mathlib's direct
`IntermediateField.finrank_sup_le` proves the required base-field inequality immediately.
Neither node realizes a statement or step of this unit's `realized` record, which is empty;
the unit's use of finite composita is preserved. No project Lean module is withdrawn.

The finite-subset construction no longer requires a separate family of singleton fields
and a second finite compositum: apply the already cited finite-algebraic-generators node
directly to the finite subset. Its Mathlib declaration is unchanged and still used.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The original plan is correct but longer than
the available Mathlib API requires. Its relative-degree and tower-law imports are redundant.
The existing docstring records that valid longer mathematical argument; the delivered node
and Lean proof record the direct Mathlib specialization instead. No consumer adaptation,
statement change, change record or new node is needed.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
