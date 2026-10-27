## What changed

Filled `WeilConjectures.publishedSystemCompositorIdentification` in
`Sheaf.SixFunctors.PublishedSystemCompositorIdentification`, following its existing
section/adjunction/localization proof plan. Added proved private helpers for
transport through equality of chosen right adjoints and for the cochain
factorization of the localized ordinary compositor. The normalization helper
keeps the derived functors, factorization isomorphisms and published comparison
isomorphisms as parameters, avoiding expensive kernel reduction inside derived
composition. Its proof identifies the direct compositors sectionwise, applies
adjunction conjugacy, then uses faithful restriction along localization. All required declarations are
already exposed by the original public import, so no imports were added.
Updated the item's node to describe the formalized argument. No public signature,
definition, attribute or public import changed.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.publishedSystemCompositorIdentification`
(node `lem-sf-published-system-compositor-identification`).
One original hole closed; zero holes added; zero holes left in the item.
No split-off statements. The final cleaned module compiled successfully in
10.7 seconds using the required remote compiler. Delivery runs the required
independent preflight checks.

## No longer needed

None. All original declared dependencies remain used. No original imports removed,
no modules withdrawn, and no unit-route steps bypassed. The proof uses the ambient
construction and section certificate; it does not require the broad
`ambientPullbackTensorCoherence` theorem itself.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The existing uniqueness lemmas
compare two published presentations; identifying the ambient presentation still
requires the prescribed section calculation. The proof supplies that calculation
and the exact-localization comparison, without moving either to a new hole.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
