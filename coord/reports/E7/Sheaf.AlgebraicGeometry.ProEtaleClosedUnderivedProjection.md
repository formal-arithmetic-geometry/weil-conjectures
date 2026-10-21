## What changed

Filled the two proofs in Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection.
The normalized adjunction uses the existing strict AsSmall construction and its proved
section formula; uniqueness is Mathlib Adjunction.ext. The projection is invertible
by closed support and localization, and natural by the tensor comparison and counit.
The coefficient objects and actions are constructed by scalar extension and transport
across that projection, with the required pure-tensor and all-section equations.
Proof-only imports add ProEtaleModuleInverseImageCanonicalUnit,
LocalizedSiteTensorRestriction, Mathlib PullbackFree and Presheaf.Sheafification.
The canonical adjunction is reused through import all; its implementation remains private.
All new helpers are private and proved. Existing public signatures and definitions
are unchanged. Updated the node proof to record the slice restriction argument.
The preflight-requested proof environment change record is
coord/changes/proetale-closed-underived-projection-proof-environment.md;
its consumer audit finds no downstream importers and no adaptations.

## Proved and sorry left

Closed both original holes (2 of 2):

- AlgebraicGeometry.ProEtaleClosedProjection.adjunction_exists.
- AlgebraicGeometry.ProEtaleClosedProjection.closed_underived_projection.

No holes added or left in the delivery; no split-off statements.
The proof uses the stated inverse-image tensor-comparison and scalar-identification
results from the existing dependency module, whose unfinished proofs remain its items.

## No longer needed

No modules withdrawn and no existing imports removed. All original proof dependencies
remain used. The open inverse-image tensor comparison in the original step 2 is replaced
by lem-sfb-localized-site-tensor-restriction, which applies directly to the overFunctor
appearing in the localization theorem. The general inverse-image comparison remains
needed for the projection itself and its naturality. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The ringed open-closed theorem supplies an arbitrary
adjunction; the proof transfers unit invertibility to the prescribed normalized
adjunction through full faithfulness and essential image. The coefficient clause can
be obtained by taking S to be the actual B-linear direct image of the constructed T
and taking p to be its identity, with eS transporting the original projection.
This avoids a separate descent proof for a B-linear map without changing any equation.
Edge cases include empty closed stratum, identity immersion, zero modules and
nonflat coefficient changes: none of the construction or proof uses flatness,
nonemptiness, or a nonzero ring.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
