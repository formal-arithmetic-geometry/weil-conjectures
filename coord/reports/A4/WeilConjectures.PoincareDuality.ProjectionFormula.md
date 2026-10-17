## What changed

Proved `boundedConstructibleExceptionalProjectionMorphism_natural_right` by
hom-extensionality for the faithful bounded-constructible inclusion and the
ambient compactification naturality theorem. The proof uses only existing
declarations and keeps every public theorem signature unchanged.

Added local, noncomputable aliases for the canonical derived monoidal structure
and its tensor data, together with local irreducibility attributes for the two
derived-functor definitions. These declarations are local to this module and
are used only to keep elaboration below the 60-second compile limit.

## Proved and sorry left

Closed one of the five original holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism_natural_right`.

Four original holes remain:

- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_openImmersionProjectionComparison`;
- `AlgebraicGeometry.ProEtale.CondensedRing.exceptionalProjectionMorphismOfCompactification_natural_right`;
- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism_natural_left`;
- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleExceptionalProjectionMorphism`.

No holes were added or split off.

## No longer needed

The private proof-cache lemmas `projectionPrecoherent`,
`projectionEssentiallySmall`, `projectionFlatResolution`,
`projectionGrothendieck`, `projectionHasTensor4`,
`projectionHasGoodTensor12`, and `projectionHasGoodTensor23` were removed;
the proof compiles without them. No repository module or DAG node is removed.

## Where the brief, the DAG or earlier work was wrong

Earlier retained work introduced public tensor-cache declarations, which the
stage-3 gate rejected. This delivery uses local aliases instead and does not
add a Sheaf module or a new postponed statement. The source contains the
retained `STATEMENT-DISPUTED` note for the unrestricted condensed-ring
isomorphism assertion; its existing hole and statement are unchanged. The
change record is `coord/changes/A4-projection-formula-derived-route.md`.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
