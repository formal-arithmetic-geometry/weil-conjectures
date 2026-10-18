## What changed

Replaced the hole in `AlgebraicGeometry.nagataMorphismDescends` with a proof comparing
maps on the pulled-back final-stage chart cover. A private proved helper uses surjective
polynomial evaluation to compare morphisms to an affine target from equality on base
sections and presentation generators. The theorem's signature and the construction are
unchanged. Updated its node's proof and proof dependencies to follow this route.

## Proved and sorry left

Closed the item's sole hole, `AlgebraicGeometry.nagataMorphismDescends`
(node `lemma-nagata-morphism-descends`), from the existing declaration interfaces.
Holes closed: 1. Holes added: 0. Holes left in the item: 0. Split-offs: 0.
The private helper `affine_ext_generators` is fully proved. No new modules, statements,
definitions, or nodes are introduced, apart from this private proof helper.

Validation: the final file compiled cleanly through `lcompile.py` in 9.2 seconds;
the theorem signature is byte-identical to its original signature, all lines are at
most 100 characters, and the retained imports pass `import_direction.py may`.
The proof continues to depend on the construction's existing named theorem obligations;
this delivery does not claim to close those dependency holes.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.NagataQCOpenDescentSpec` and
`Sheaf.RingTheory.FilteredColimitFiniteData`. Removed direct proof dependencies
`lemma-nagata-qc-open-descends` and `lemma-nagata-filtered-colimit-finite-data` from this
node. The former's cover consequences are already supplied by `data.charts_cover`;
the latter's lifting consequences are already fields `generatorLift_eq` and
`coefficientLift_eq`. Both remain dependencies of the underlying construction where
needed; this delivery does not claim that either entire module leaves the targets' closure.
No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan repeated the construction's open-descent and finite-data
arguments even though its Lean record already retains their necessary consequences.
The current blueprint's chart comparison and gluing route is preserved. No statement
or definition repair was necessary. The finite cover may be empty: `charts_cover` then
forces its source, and hence its base change, to be empty, so cover extensionality still
applies. The affine comparison also permits zero generators, because polynomial
surjectivity and equality on base coefficients suffice in that case.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
