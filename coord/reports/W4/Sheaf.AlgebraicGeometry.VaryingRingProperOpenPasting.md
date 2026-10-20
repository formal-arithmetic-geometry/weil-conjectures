## What changed

Proved the image component identity in `modulePi_components` by the adjunction triangle identity and the invertibility of `moduleOpenToP`. Split the complementary-component vanishing into the new theorem `modulePi_complement_zero` and imported it.

## Proved and sorry left

Closed the image-component part of `modulePi_components`; the declaration is now proved from the image calculation and `modulePi_complement_zero`. The new theorem `modulePi_complement_zero` remains `sorry`. The existing declarations `moduleAlpha_vertical`, `moduleAlpha_horizontal`, `alpha_identities`, and `gamma_evaluation` retain their pre-existing `sorry`s.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the image and complementary-component calculations into one theorem. The image calculation is a short adjunction argument, while the complementary restriction requires the separate sheaf localization argument; it is recorded as a new lower node.

## New nodes

`new-lem-sp-varying-ring-module-pi-complement-zero` records the complementary-component vanishing used by `modulePi_components`.

The split is recorded in `coord/changes/varying-ring-module-pi-complement-zero.md`.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
