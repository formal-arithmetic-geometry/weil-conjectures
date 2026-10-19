## What changed

Proved `AlgebraicGeometry.Etale.properSupport_geometricStalk_image_core` with its existing signature and visibility. All helpers are private and proved in the item module. The proof establishes proper support under fibre restriction, proves the kernel assertion using the closed support image, lifts fibre sections by proper base change and Nagata compactification, and handles arbitrary bases by affine-open localization. Explicit unit, counit, comparison and base-change calculations ensure that every constructed lift maps to the given section.

Added proof-only imports for the existing proper geometric-point exchange, support-image and support-range APIs, extension-by-zero base change, and the open-closed exact sequence. The public imports match the current shared source. Updated the existing node's proof, proof dependencies and proof origin to describe the actual argument. No definitions, public signatures or consumers changed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Etale.properSupport_geometricStalk_image_core` (node `lem-cbc-proper-support-geometric-stalk-image-core`). Original holes: 1. Holes added: 0. Holes remaining in the delivery: 0. No statements were split off. The complete module compiled through `lcompile.py`; the delivery dry run also checks the final packet.

## No longer needed

Removed the original direct imports `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`, `Sheaf.AlgebraicGeometry.ClosedProperSupportLocality`, `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`, and `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`. Removed the redundant direct import `WeilConjectures.SixFunctors.OpenClosed.Complex`, which is publicly imported by the required exactness module. Also removed the exploratory proof import `WeilConjectures.SixFunctors.BaseChange.Pasting`.

The direct planned dependencies `lem-weil-pbc-inverse-image-stalk-germ`, `lem-cbc-closed-proper-support-locality`, `lem-weil-pbc-reduced-induced-closed-subscheme`, `lem-weil-pbc-extension-by-zero-unit-iso`, `lem-weil-pbc-extension-by-zero-stalks`, and `lem-weil-pbc-separated-base-change` are not used as declarations in this proof. The module-valued germ identity is proved from the categorical point-comap API. Closed support calculations use `closed_subset_proper_over_base_properties` and the canonical reduced closed subscheme directly. The existing open-extension support-range, open-closed exactness and extension-zero base-change APIs supply the needed extension properties. Only proper geometric-point exchange is needed for the ambient proper morphism. These are removals of direct proof dependencies; this report makes no claim that their modules disappear from the whole targets' transitive import closure.

## Where the brief, the DAG or earlier work was wrong

The planned inverse-image stalk-germ declaration is specialized to abelian-group sheaves, while this statement uses module sheaves. Its categorical argument generalizes directly and is proved privately here. The original one-step plan also left affine-base localization implicit: Nagata's hypotheses require the explicit quasi-compact quasi-separated base reduction supplied by this proof. Neither issue requires any statement or definition repair. The unit route is retained; the unit record has no realized steps to change.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
