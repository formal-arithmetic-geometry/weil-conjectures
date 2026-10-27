## What changed

Proved `WeilConjectures.IntegralSystemRealization.systemPushIdentityPullUnit` in
`Sheaf.SixFunctors.SystemPushIdentityPullUnit`, preserving its exact statement and
public import. The witness is localization of the ordinary inverse-image identity
adjoint to the bridge-normalized direct-image identity. The sectionwise unit law
and exact localization prove its compositor equation; adjoint uniqueness and
conjugation of composites prove its bridge-mate equation.

Added proof-only imports of `IntegralSystemCompositorAssociativity`,
`StrictTowerDirectImageCoherence`, and the source library's
`AdjunctionSquareComposition`, reusing their proved private normalization,
localization, site-unit, and conjugation helpers. Updated the item's DAG proof and
proof dependencies to record these actual uses. No other existing module changes.

Validation: the final module compiles cleanly through `lcompile.py` in 23.7 seconds.
The theorem signature is byte-for-byte unchanged, there are zero textual `sorry`s,
all lines meet the 100-character limit, and all three added imports pass the
repository import-direction check.

## Proved and sorry left

Closed 1 of 1 holes:
`WeilConjectures.IntegralSystemRealization.systemPushIdentityPullUnit`
(node `lem-sf-system-push-identity-pair-pull-unit`).

No holes remain in the delivered module. No holes were added or split off.
All local helper theorems are proved.

## No longer needed

None. The original bridge import and the original proof dependencies remain
necessary. No module, declaration, or node was withdrawn. The additional imports
are private proof dependencies. The blueprint unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan omitted the explicit ordinary site-unit,
adjunction-comparison, and localization identifications. Existing proved helpers
supply these steps, so this twice-split obligation needs no further decomposition.
The rework archive was read before restoration; its declaration, dependency, and
DAG attachment are preserved. The current published build already provides the
bridge and operation dependencies, and the archived item statement compiles.

The DAG source path lists both tags under `more-etale.tex`; Tag 07A7 is actually
`sites-cohomology.tex`, Remark `remark-base-change`. Tag 0F7C is in
`more-etale.tex`. This citation-path issue does not change the statement or proof.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
