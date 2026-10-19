## What changed

Proved `IsDiscreteValuationRing.inertia_order_prime_part` with its signature unchanged,
following all five steps of `lem-exc-dvr-inertia-order-prime-part` and Stacks Tag 09EE,
first proof paragraph. The existing global degree data and normal residue action
supply the geometric inputs. The proof compares the supplied uniformizer exponent
with the degree-data exponent using the DVR additive valuation, counts the orbit
and the kernel, retains the inseparable residue degree, and identifies `n` with
`ordCompl[p] e`.

Only the item module changes. Additional Mathlib imports are private proof imports.
No definitions, statements, consumers, or DAG routes change.

## Proved and sorry left

Closed the one original hole:
`IsDiscreteValuationRing.inertia_order_prime_part`
(node `lem-exc-dvr-inertia-order-prime-part`).

No holes remain in the item, no holes were added, and no statements were split off.
The proof uses the existing declarations `NumberTheory.dvr_galois_degree_data`
and `IsDiscreteValuationRing.residue_normal_action`; their proofs are separate items.

## No longer needed

None. Both original proof imports and all four declared proof dependencies are used.
The unit's route is preserved. No modules or nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The prime-fibre action supplied by Mathlib
uses `galRestrict`, whereas the ideal action uses the direct action on the integral
closure. Their agreement is proved explicitly inside the proof.

The searches via Lean Finder, Loogle, and grep confirmed that Mathlib's direct
inertia-cardinality formulas require perfect or separable residues and do not apply
to this statement. The arbitrary normal residue extension instead contributes its
inseparable degree, a power of `p`, exactly as the node prescribes.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
