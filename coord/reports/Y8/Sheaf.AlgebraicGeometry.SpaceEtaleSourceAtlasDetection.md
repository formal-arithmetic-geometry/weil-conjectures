## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.etale_source_atlas_detection` with its exact
original statement. Added two fully proved private pullback-square helpers: transfer
scheme properties between representing tests via Yoneda and base-change scheme-test
predicates by pullback cancellation. The proof first descends scheme-source etaleness,
then handles arbitrary representable source covers, derives the atlas equivalence,
and extracts atlas existence from the algebraic-space property.

Added the private proof import AlgebraicSpaceRepresentableEtaleSchemeTests and updated
the existing node's proof and proof dependencies to match. No new nodes or modules.
Validation: the final module compiled without warnings in 6.8 seconds; its unchanged
direct consumer `ChartwiseEtalePermanence` compiled against it without warnings in
9.1 seconds. The consumer copy was removed from the delivery after checking.
The theorem statement was checked byte for byte against the original.
The import change is recorded in
`coord/changes/Y8-space-etale-source-atlas-proof-imports.md`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.AlgebraicSpace.etale_source_atlas_detection`
(node `lem-trf-space-etale-source-atlas-detection`). Added 0 holes; 0 holes remain
in the delivered module. Both private helpers are fully proved. The proof uses the
already stated `representable_etale_scheme_tests` and `isEtale_comp`, which still
have upstream holes; this delivery does not claim to close those dependencies.

## No longer needed

Removed public imports `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`
and `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`. The proof needs no
bundled algebraic-space fibre products: its existing representing squares suffice.
Removed `lem-trf-space-fibre-products-etale-covers` from this node's proof dependencies;
it remains a statement dependency and is still imported by other consumers and by the
scheme-tests dependency, so no whole module is claimed pruned from the target closure.
No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's step 2 can be implemented more directly for
arbitrary presheaves by pullback-square cancellation; no algebraic-space structure on
the fibre product is needed. Surjectivity and etaleness in the definitions may choose
different representing schemes, so their identification must explicitly use uniqueness
of pullbacks and Yoneda. Empty schemes are covered by the general descent theorem;
no nonempty, separatedness, finiteness or Noetherian hypotheses were introduced.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
