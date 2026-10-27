## What changed

Proved `LinearMap.fittingIdealZero_prod` from the stated presentation-independence theorem.
Four proved private helpers normalize zeroth presentation ideals to full determinants,
insert a determinant generator, establish the block-row determinant inclusion, and identify
the chosen ideal with any surjective presentation. The proof chooses two finite presentations,
constructs their product presentation, and proves both ideal inclusions.

The forward inclusion expands each row into its left/right supported components. For a
nonzero summand, a nonzero Leibniz term supplies the permutation arranging its rows into a
block diagonal matrix. Its determinant is a product, up to a unit sign. The reverse inclusion
uses a block diagonal matrix of arbitrary determinant generators and `Ideal.span_mul_span`.
Empty presentations and zero rings are included; no domain or finite-presentation assumption
was added. Updated the existing node's proof to describe this argument.

Converted the legacy item and its unclaimed dependency `FittingIdealZero` to module format.
The latter's definition signature and body remain verbatim; its existing imports stay public.
The item publicly imports its statement dependency and privately imports ideal operations.
Change record: `coord/changes/D5-fitting-ideal-module-format.md`.

## Proved and sorry left

Closed 1 hole: `LinearMap.fittingIdealZero_prod`
(node `lem-trf-fitting-ideal-direct-sum`). Added 0 holes; split off 0 statements.
No sorry remains in either delivered Lean file. The proof still uses the pre-existing
`LinearMap.presentationFittingIdeal_independence_baseChange` sorry from its declared dependency;
this delivery does not claim to close that dependency.

## No longer needed

Removed redundant direct imports `Sheaf.RingTheory.PresentationFittingIdeal` and
`Mathlib.RingTheory.Finiteness.Prod`: both are exported by `FittingIdealZero`.
No DAG dependency or module is pruned: finite generation, presentation independence and the
determinant remain used. No new combinatorial or minor-ideal statement is needed.

## Where the brief, the DAG or earlier work was wrong

The item and FittingIdealZero had not yet been converted to module format, despite the
project-wide format requirement. The initial module compile exposed this and both files
are converted in the packet. The DAG's proposed grouping of permutations is valid but
unnecessary: row multilinearity and one nonzero permutation term give the required ideal
inclusion more directly. All statements and the unit route are preserved.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
