## What changed

Proved `CategoryTheory.hypercohomologyCouple` by constructing the canonical
`BigradedExactCouple` from `hypercohomology_maps_exact`. The construction uses the
three maps and the six exactness/zero-composite clauses directly, matching the
source exact-couple structure. Removed the two unused private page-transport
helpers `couple_iso_pages` and `exact_couple_pages`; all of their consumers were
inside the withdrawn `hypercohomologyFiltrations_spec` proof block.

## Proved and sorry left

Closed the `hypercohomologyCouple` definition hole. No `sorry` remains in the
delivered module and no new theorem or hole was added.

## No longer needed

The private helpers `couple_iso_pages` and `exact_couple_pages` were unreachable:
the only references were in the commented-out exact-functor specification proof.
No imported module was removed; all imports remain needed by declarations retained
in this module. The interface change is recorded in
`coord/changes/hypercohomologyCouple.md`.

## Where the brief, the DAG or earlier work was wrong

The module still contained two private page-comparison helpers whose declarations
were no longer reachable after the upstream synchronization removed the public
specification theorem. Treating those dead private declarations as obligations
would add unsupported proof work without affecting any exported declaration.

## New nodes

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
