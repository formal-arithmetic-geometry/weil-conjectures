## What changed

Completed `Algebra.equivariant_prefix_finite_chain_homotopy` in the assigned module.
Private proved helpers compute the boundary, insertion, translation and recursion on basis
chains; transfer the existing augmented power-set contraction identities; establish the
cycle and homotopy identities by induction; and prove equivariance, finite-list evaluation,
continuity and preservation of coordinate forms. The final theorem specializes these
inductions to each finite initial segment.

Added proof imports `Mathlib.Tactic.Abel`, `Mathlib.Algebra.BigOperators.Fin` and
`Mathlib.Algebra.BigOperators.GroupWithZero.Action`. All original definitions, public
imports and the theorem signature are unchanged. No other existing module was changed.
The proof follows all eleven steps of the existing node, so its route and dependencies
are unchanged.

## Proved and sorry left

Closed the one original hole in `Algebra.equivariant_prefix_finite_chain_homotopy`
(node `lem-sfb-equivariant-prefix-finite-chain-homotopy`). Added no holes and split off
no statements. No `sorry` remains in the delivered module. Every private helper is proved.

Validation: `lcompile.py` compiled the full module cleanly, with no warnings,
in 8.4 seconds (exit code 0). The public theorem signature and all original definitions
were also compared verbatim with the shared source and found unchanged.

## No longer needed

None. No imports, nodes or modules were pruned. The free integral basis and existing
power-set contraction dependencies are used by the proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The augmented empty-tuple case is proved explicitly,
and the recursive identity uses only the stated finite segment of A. List induction includes
the empty list in length zero; it requires no equality comparisons on evaluated tuples.
Continuity is proved from product projections and composition, while the coordinate-form
induction only uses selection of input indices and adjoining coordinate zero.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
