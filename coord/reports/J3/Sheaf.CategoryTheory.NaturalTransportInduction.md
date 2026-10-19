## What changed

Proved `CategoryTheory.NaturalTransport.compared_eq` in
`Sheaf.CategoryTheory.NaturalTransportInduction` by induction on the predecessor of the
positive transport index, following all four steps of
`lem-trf-frobenius-transport-induction`. The base case uses the normalized comparison
and equality transport. In the successor case, inverse cancellation recovers the
repeated composite from `compared`; naturality moves the comparison across `η`,
and the component of `hdb` gives the prescribed successor recurrence.
All existing signatures, definitions, docstrings, and imports are unchanged.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.NaturalTransport.compared_eq`
(node `lem-trf-frobenius-transport-induction`). No holes added or split off.
No `sorry` remains in the delivered module. The three existing definitions remain
explicit recursive constructions/composites.

## No longer needed

None. Both existing public Mathlib imports are used by the statements. The proof
uses only Mathlib category laws, functoriality, naturality, and isomorphism identities,
so it needs no additional imports. The declared dependency `def-nagata-category`
is retained as the Mathlib category leaf. No node or module is pruned; the DAG
proof and the unit route are unchanged.

## Where the brief, the DAG or earlier work was wrong

No discrepancy found. The index `n` represents source index `r = n + 1`.
The proof requires no naturality hypothesis on `τ` and no invertibility hypothesis
on `η`. It applies to arbitrary categories, including the empty category, and its
base case retains the explicit equality transport when `P 0 = T` is not reflexive.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
