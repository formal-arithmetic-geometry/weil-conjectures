## What changed

Proved `WeilConjectures.PurStrictScalar.scalarConstantRestriction_complete_map_injective`
without changing its statement or public imports. Added private proof imports and proved
private helpers for the completion argument and the normalized coefficient comparisons.
Updated the existing node's proof, proof dependencies and proof origin to this route.

In the small-site model, factor maps into the complete target through the completed-side
completion unit. Use the restriction/completion comparison, preserving units, and the
constant-side reflector universal property to detect equality of the factorizations.
Faithfulness of restriction between complete objects then proves equality of the original
maps. Transport this argument through the native and detailed coefficient equivalences.
The quotient-projection calculation verifies the actual scalar map used by the theorem.
The given derived-category instance for constant modules is retained throughout.
The full proof compiled in 24.9 seconds; the sole redundant-tactic warning was removed
before the final delivery checks.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.PurStrictScalar.scalarConstantRestriction_complete_map_injective`
(node `lem-pur-complete-constant-restriction-map-injective`).
No holes remain in the delivered module. No holes were added or split off.
The proof uses existing stated results, including the constant-completion reflector and
restriction/completion comparison; it does not claim to close those imported obligations.

## No longer needed

No original imports were removed and no modules were withdrawn.
The original node's direct dependency on
`lem-weil-pbc-completed-constant-presentation-transport` is replaced by the more explicit
small-site coefficient and Koszul-completion comparisons. That node may remain needed
transitively elsewhere, so no global withdrawal is requested.
The proposed derived-coinduction object and its unit calculation are unnecessary:
the existing two completion reflectors and the equivalence on complete objects suffice.

The nodes `lem-weil-pbc-completed-constant-coefficient-equivalence`,
`lem-weil-pbc-completed-koszul-constant-transport`,
`lem-weil-pbc-ringed-topoi-module-adjunction`,
`lem-weil-pbc-integral-coefficient-completeness-transport`, and
`def-sfb-integral-completed-coefficient-transport` are used as coefficient/completion
tools from their existing units. No statement or step of the item's blueprint unit is
bypassed; no node of that unit supplies these coefficient comparison tools.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original proof plan was longer than necessary: injectivity
for arbitrary source follows from the completion universal properties and the already
stated equivalence on complete objects, without constructing derived coinduction.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
