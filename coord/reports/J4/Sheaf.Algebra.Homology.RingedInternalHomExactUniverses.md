## What changed

Proved `CategoryTheory.RingedHomUniverses.ringedInternalHom_exact` in
`Sheaf.Algebra.Homology.RingedInternalHomExactUniverses`, without changing its
statement, universes, public imports, or definitions. Added the private proof
import `Sheaf.CategoryTheory.SignedDerivedInternalHomExact`.

The contravariant conjunct retains the coherent shift and triangulatedness from
`CategoryTheory.signedDerivedInternalHom_exact`; its section functor is
definitionally the flipped curried functor in this item. The covariant conjunct
uses `homCommShift` and `hom_isTriangulated` from the existing shift module.
Updated the node's proof, proof dependencies and proof origin accordingly.
The single-file launcher compile passed in 5.0 seconds (exit code 0).

## Proved and sorry left

Closed the sole hole:
`CategoryTheory.RingedHomUniverses.ringedInternalHom_exact`
(node `lem-weil-pbc-ringed-internal-hom-exact-universes`).

Original holes: 1. Closed: 1. Added: 0. Remaining in the delivered module: 0.
No split-off statements, new definitions, or axioms were added.

## No longer needed

No imports removed and no modules or nodes withdrawn. The original declared
proof dependency `lem-weil-pbc-ringed-internal-hom-exact-restriction` remains
needed for normalized covariant exactness. A separate independent-universe
contravariant cone calculation in this module is unnecessary: the already proved
`lem-coef-signed-derived-internal-hom-exact` supplies it with stronger normalization.
No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan did not name the existing independent-universe
signed contravariant exactness theorem. The updated proof explicitly cites that
proved node instead of repeating its cone argument. The recorded unit name
`sk-prop-weil-pbc-ringed-internal-hom-exact-restriction` has no corresponding
file under `dag/units`; no unit record is changed by this delivery.

Library searches found the direct route in `SignedDerivedInternalHomExact` and
`RingedInternalHomShiftOfUniverses`; the logged LeanFinder and Loogle searches
returned generic triangulated adjunction and shift APIs. Stacks Tag 08JC states
exactness in both variables, matching the unchanged conjunction here.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
