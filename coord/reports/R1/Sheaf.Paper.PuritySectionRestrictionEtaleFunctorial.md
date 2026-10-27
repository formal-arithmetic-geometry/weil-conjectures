## What changed

Filled `restrictionEtale_functorial` with the explicit coherence proof.  The proof
establishes exceptional-compositor associativity, the composition law for the
finite-etale normalization comparison, and pullback coherence for section maps;
it then derives the composite law and identity law for `restrictionEtale`.
The item module is the only Lean file changed in this delivery.

## Proved and sorry left

Closed the sole `sorry`: `WeilConjectures.PurityFiniteSetting.SectionRestriction.restrictionEtale_functorial`.
No `sorry` remains and no statements were split off.

## No longer needed

None.  The proof uses the finite-etale dualizing normalization and ordinary-etale
upper-star composition interfaces recorded by the item node; no additional
planned dependency was removed.

## Where the brief, the DAG or earlier work was wrong

None.

## New nodes

None.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
