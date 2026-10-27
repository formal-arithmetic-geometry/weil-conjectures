## What changed

Reduced `AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_fiber_iso_spread`
in the assigned module to a fibre homomorphism lifting step, with the original signature and
all public imports preserved. Added only private proof imports. The main proof establishes
properness, uses the existing finite-locally-free isomorphism-locus reflection theorem, removes
the closed image of the complement of that locus, and explicitly transports the resulting
isomorphism through tensor-pullback composition. No existing shared interface was changed.
Both modules compile through `lcompile.py`; the final assigned-module compile took 6.1 seconds,
and the lifting module took 6.2 seconds in the preceding import-order compile.

The new module `Sheaf.AlgebraicGeometry.ProjectiveBundleFiberHomLift` isolates the lifting
part before proper shrinking. It supplies a morphism above a neighbourhood whose pullback
to the single fibre is invertible. The main proof constructs a smaller neighbourhood where
the morphism itself is invertible. This is a genuine step of the old argument, rather than
another assertion of an isomorphism above a neighbourhood.

## Proved and sorry left

Original holes: 1. Upper holes closed by reduction: 1, namely
`AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_fiber_iso_spread`.
Direct proofs without newly split obligations: 0. Added holes: 1, namely
`AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_fiber_hom_lift`
(node `lem-sfb-projective-bundle-fiber-hom-lift`). Thus this delivery is a decomposition,
with zero net holes closed, rather than a claim of a completed independent proof.
The assigned module has zero remaining `sorry`; the new module has exactly one.
The existing `AlgebraicGeometry.projectiveBundle_proper` is used as stated, including its
existing unproved body; this delivery neither changes it nor adds that hole.

The new statement has a source and a complete proof plan in its docstring and node. Its
remaining work is the Noetherian section lift (including the H1 and flatness identifications)
and its transport through arbitrary-base approximation. Empty bases have no point to check;
nilpotents are allowed, and no reducedness, connectedness or global quasi-compactness is added.

## No longer needed

No module or node is globally pruned, and no original import is removed. The original
Noetherian lifting and limit-descent dependencies remain needed by the new lifting node.
They are removed only from the assigned node's direct proof dependencies and moved into
that node: `lem-trf-projective-bundle-quotient-geometry`,
`lemma-nagata-projective-space-base-change-proper`, `lem-nagata-polynomial-projection-flat`,
`lem-pc-projective-space-twist-cohomology`, `lem-sfb-proper-flat-fibre-section-lifting`,
`lem-weil-pbc-module-pullback-tensor`, `lemma-nagata-noetherian-inverse-system-affine`,
`lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-limit-fibre-products`,
`lem-trf-invertible-affine-limit-descent`, `lem-weil-pbc-limit-residue-field`, and
`lem-trf-fp-module-limit-isomorphism-descent`. None is declared mathematically unnecessary.
The proper-shrinking step uses the existing module-map isomorphism-locus API instead of
introducing a new section generation or tensor-dual trivialization statement.

## Where the brief, the DAG or earlier work was wrong

EGA II Remark 4.2.7 announces the locally Noetherian projective-bundle Picard classification;
it does not give the detailed lifting/shrinking proof attributed to it in the old node.
The Stacks Project perfect-direct-image result and invertible-limit descent supply the
sources of the lifting argument. The original mathematical statement is retained unchanged.
No tool failure, definition repair, source-library edit or consumer adaptation is involved.

## New nodes

`lem-sfb-projective-bundle-fiber-hom-lift` belongs to the same chapter and unit, and inherits
the original blueprint ancestry with the assigned node prepended. It records the lifting
step before proper shrinking, with its original Noetherian and approximation dependencies,
three kinds of searches, its Lean signature, and edge-case checks. The unit route is preserved.
No change record is needed because all existing signatures and definitions are unchanged.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
