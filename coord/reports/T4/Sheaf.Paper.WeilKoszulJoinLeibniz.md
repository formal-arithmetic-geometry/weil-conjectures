## What changed

Completed `koszulJoinSummand_leibniz_nonpositive` in
`Sheaf.Paper.WeilKoszulJoinLeibniz`. Private exterior-coordinate helpers identify
summand multiplication and differentials with exterior multiplication and
contraction. The head and tail calculations include exterior degree zero.
The proof then evaluates on pure tensors and applies the existing graded
contraction Leibniz identity, with the cochain sign converted to `(-1)^n`.
The two item nodes now describe this proof and the existing positive-degree assembly.
No signatures, public definitions, attributes, or imports changed.

Validation: the complete item module compiled through `lcompile.py` without
warnings in 14.7 seconds. Both public theorem signatures and the imports were
compared against the repository source and are unchanged; all Lean lines are
within 100 characters.

Searches: LeanFinder and Loogle found Mathlib `HomologicalComplex.extend_d_eq`.
The grep search confirmed the extension and `negOnePow` APIs. Source-tree searches
found the existing local algebraic Leibniz proof and the parallel coordinate
calculations in `WeilKoszulJoinBijectiveNonpositive`; no stronger theorem is needed.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.Scheme.koszulJoinSummand_leibniz_nonpositive`
(node `lem-weil-pbc-koszul-join-summand-leibniz-nonpositive`).
The already proved `AlgebraicGeometry.Scheme.koszulJoinSummand_leibniz` now uses
that complete proof. Holes closed: 1 of 1. Holes added: 0. Sorry left: none.

## No longer needed

None. The existing public import is needed by the statements and the proof.
No dependency module or unit-route node is pruned. The differential node remains
needed by the nonpositive proof, although the general theorem now records its
immediate dependency on the nonpositive theorem explicitly.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement needed repair. The general equation's node had not
recorded its existing immediate dependency on the nonpositive case; its proof
and dependency list now agree with that assembly. The remaining obligation is
closed directly rather than split again.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
