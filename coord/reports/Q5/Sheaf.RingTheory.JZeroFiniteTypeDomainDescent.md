## What changed

Proved `RingHom.exists_nonempty_regular_open_of_finiteType` in
`Sheaf.RingTheory.JZeroFiniteTypeDomainDescent`, with its signature unchanged.
Choose a regular principal open in the target, apply the existing proved generic-freeness
lemma to its coordinate ring, identify its module localization with its ring localization,
and apply regular faithfully flat descent. A nonzero-domain localization supplies the
nontriviality required by Mathlib's free-module faithfully-flat instance. The resulting
principal open of the base contains the zero prime and has regular local rings.

Added proof imports for principal-localization finite type, iterated localization,
extending scalars of a linear equivalence, and the ring/module localization comparison.
Updated the existing DAG node to match the proof. All seven mathematical steps remain;
there are no new declarations, statement changes, definition changes or consumer adaptations.

Validation: a fresh server file check passed without warnings in 9.5 seconds.
The proof was checked against the current dependency signatures and the local source
`more-algebra.tex`, `lemma-J-0-goes-down`; the existing seven-step route is preserved.
`#print axioms RingHom.exists_nonempty_regular_open_of_finiteType` reported exactly
`propext`, `Classical.choice`, and `Quot.sound`. Removed that diagnostic command afterwards.

## Proved and sorry left

Closed the only hole, `RingHom.exists_nonempty_regular_open_of_finiteType`
(node `lem-exc-j0-finite-type-domain-descent`). Proved 1 of 1; zero holes remain in the
item, zero holes added, and zero split off. This is a proof, not a decomposition.
The axiom check also confirms that no imported unfinished theorem is used transitively.

## No longer needed

Removed proof import `Sheaf.RingTheory.LocalizationOfRegularRing` and dependency
`lem-weil-pbc-localization-of-regular-ring`, including its obsolete tool approval.
At each prime of the localization, Mathlib's canonical iterated-localization isomorphism
transports regularity directly. The existing Mathlib-leaf node
`lem-weil-pbc-localization-of-localization` records this replacement.

Removed proof import `Sheaf.AlgebraicGeometry.IsRegularScheme`: this argument uses only
Mathlib's ring predicates, already publicly imported; it never uses regular schemes.
The node `def-weil-regular-scheme` remains needed for its ring clauses.

Removed redundant proof imports `Mathlib.GroupTheory.MonoidLocalization.Away`,
`Mathlib.LinearAlgebra.FreeModule.Basic`, `Mathlib.LinearAlgebra.TensorProduct.Defs`,
and `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: the needed declarations are available
through the retained imports. Their definition nodes remain applicable to the argument.
No other nodes or modules are made unnecessary by this proof; the project's unit route stays.
Public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The longer explicit fraction and basis calculations in the
plan already have suitable Mathlib APIs. In particular the nontrivial-free faithfully-flat
instance supplies the infinite-basis argument without an additional theorem. The initial
remote compiler process ended without diagnostics during the interruption; the subsequent
server checks returned normally and validated the proof.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
