## What changed

Filled two existing helper proofs in
`lean/Sheaf/Paper/FiniteFreeSystemRestriction.lean`:
`WeilConjectures.FiniteFreeSystemRestriction.levelMap_transition` reduces the
ring-homomorphism equality to representatives of the source quotient, where both
composites are definitionally the residue of the integral inclusion.
`WeilConjectures.FiniteFreeSystemRestriction.inverse_compatibility` cancels the
lower hom isomorphism, substitutes the given hom square, and cancels the mapped
upper inverse/hom pair using functoriality.

The existing signatures, definitions, docstrings and proof plan are preserved.
The revised file compiled successfully on the server in 24.3 seconds; temporary
profiling options were removed before delivery. The delivery tool validates the
final file and its declaration axioms.
This is a partial delivery for the three-hole module, as permitted by the brief.

## Proved and sorry left

Closed 2 of the 3 original holes:

- `WeilConjectures.FiniteFreeSystemRestriction.levelMap_transition`.
- `WeilConjectures.FiniteFreeSystemRestriction.inverse_compatibility`.

One original hole remains unchanged:

- `WeilConjectures.FiniteFreeSystemRestriction.finiteFreeSystemRestriction`
  (node `lem-coef-finite-free-system-restriction`). Its docstring and node retain
  the full scalar-normalization, geometric-comparison and compactification proof
  plan. This delivery does not claim to have proved that existence theorem.

Added 0 holes; split off 0 statements. Both helper proofs introduce no new
mathematical assumptions. Quotient compatibility includes n = 0. The inverse
argument applies to every indicated derived-system object and does not use
conservativity, evaluation, or any additional invertibility assertion.

## No longer needed

None. No new imports were added. The original imports and outstanding main
proof dependencies are retained; the two helpers use the already available
quotient and category-theory API. No module or DAG node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed for the two helper statements. LeanFinder
returned `CategoryTheory.CommSq.horiz_inv` as a generic inverse-square lemma;
Mathlib quotient extensionality and the elementary isomorphism cancellation
identities suffice directly. The main existence assertion remains open.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
