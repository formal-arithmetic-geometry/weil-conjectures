## What changed

Replaced the sole sorry in `TraceFormula.ciLocalRingPrincipalNeighbourhood` with the
four-step argument already recorded in its DAG node. A finite polynomial presentation
identifies the original algebra with a quotient. Localization of that quotient supplies
a surjective map from the regular polynomial local ring. The given presentation gives
a second surjective local map with the stated regular-sequence kernel. Applying
`TraceFormula.essentiallyFiniteTypeCIKernelInvariance` produces the regular sequence
needed by `Algebra.exists_globalCompleteIntersection_of_regularSequence`. Finally,
the quotient equivalence transports the principal localization, its polynomial
presentation, and its Krull dimension to the original algebra.

All declaration signatures, imports, and definitions are unchanged.
The final module compiled cleanly through `lcompile.py` in 10.5 seconds,
with no errors or warnings.

## Proved and sorry left

Closed 1 of 1 holes: `TraceFormula.ciLocalRingPrincipalNeighbourhood`
(node `lem-trf-ci-local-ring-principal-neighbourhood`). Added 0 holes and split off
0 statements. No sorry remains in the delivered module.

The proof uses the existing statement
`TraceFormula.essentiallyFiniteTypeCIKernelInvariance`, whose own proof remains
sorry in its existing module; that module is unchanged by this delivery.

## No longer needed

No original imports removed; two redundant experimental proof imports
(`Mathlib.RingTheory.Localization.Ideal` and
`Mathlib.RingTheory.LocalRing.RingHom.Basic`) were discarded before delivery.
All six dependencies in the existing node's proof plan are used; no node,
module, or original import is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical corrections were needed. Localization of a quotient requires an
explicit compatibility proof for the scalar tower from the base field through
the polynomial quotient; this is proved directly from the algebra maps.
The proof allows an empty regular sequence and zero polynomial variables and
keeps the independent universes of the field, algebra, and regular local ring.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
