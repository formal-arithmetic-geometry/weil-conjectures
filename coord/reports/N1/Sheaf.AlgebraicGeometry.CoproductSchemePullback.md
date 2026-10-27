## What changed

Proved `AlgebraicGeometry.Scheme.fppfSheaf_coproduct_scheme_pullback` in
`Sheaf.AlgebraicGeometry.CoproductSchemePullback`, preserving its exact signature
and docstring. All helper theorems and two helper constructions are private and
fully proved. Updated the existing node's proof to describe the implemented route.

The proof derives the geometry of a supplied scheme coproduct directly from its
universal property, even with a large index type. The nonempty component pullbacks
have a small support because their indices inject into the test scheme. It forms
the actual coproduct of this support and restores empty summands by initiality.
The existing `fppfSheaf_coproduct_partition` supplies the cartesian summand squares.
Local lifts are glued along a disjoint open cover, and the presheaf pullback is
verified pointwise, including uniqueness and the inverse-image-open equality.

Removed the unused public AlgebraicSpace import and made the scheme Limits import
private. Change record: `coord/changes/N1-coproduct-scheme-pullback-imports.md`.

Validation: the final file compiles through `lcompile.py` with exit code 0, without
warnings, in 14.0 seconds. The proof treats arbitrary index and coefficient universes;
empty families and empty summands are handled by the same constructions. No global
build or source-library modification was performed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.fppfSheaf_coproduct_scheme_pullback`
(node `lem-trf-coproduct-scheme-pullback`).

The item has zero remaining textual `sorry`s. Added zero holes and split off zero
statements. Its proof uses the pre-existing admitted theorem
`AlgebraicGeometry.Scheme.fppfSheaf_coproduct_partition`; this dependency remains
necessary and was not changed. This is a proof from the declared dependencies,
not a claim that their admitted proofs have been completed.

## No longer needed

Removed the import `Sheaf.AlgebraicGeometry.AlgebraicSpace`: no algebraic-space
notion is needed by either this statement or its proof. Its public definitions
are no longer re-exported here. The proof-only API from
`Mathlib.AlgebraicGeometry.Limits` is now imported privately. The temporary extra
`Mathlib.CategoryTheory.Limits.Types.Pullbacks` import was removed after confirming
it is already available through the retained imports.

No DAG proof dependency was pruned: the existing partition theorem, scheme-coproduct
Mathlib leaf and scheme-morphism-gluing Mathlib leaf are all used. No module is
withdrawn. Both DAG parents and the unit route remain intact.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the statement or planned argument. The large
index universe requires more than the generic small-family coproduct instance;
the docstring already notes this issue, and the proof implements its small-support
argument. The supplied large-family coproduct cofan also requires a direct argument
for its open inclusions, covering and disjointness. These have been proved privately
rather than adding a smallness hypothesis. The old public AlgebraicSpace import was
unnecessary, as already noted by the stage-2 reviewer.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
