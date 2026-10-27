## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.finite_qc_atlas_assembly` in
`lean/Sheaf/AlgebraicGeometry/SpaceFiniteQcAtlasAssembly.lean`, preserving its entire
statement and all public imports. Added only proved private helpers in the same module.
The sheaf coproduct argument adapts the already-proved private construction in
`AlgebraicSpaceCoproduct` to a small index type in an arbitrary universe. It uses
Mathlib's `GrothendieckTopology.isColimitCofanMkYoneda` to construct the actual atlas map
and prove its restriction and uniqueness equations.

Scheme-source representability comes from `representable_etale_scheme_tests`.
Mathlib's relative morphism-property API proves that every component map to the space is
etale. Pulling back the summand open cover proves etaleness of every scheme test locally
on the source. For surjectivity, pull back the cover of Z to the test scheme, lift through
the given local atlas, and use the representing pullback's universal property. The
finite open-cover compactness theorem supplies the quasi-compactness clause.

Updated the item's DAG proof, proof dependencies and proof origin to this argument.
The empty index type and empty individual summands require no special branch: the
empty-cover sheaf axiom and the base-changed jointly-surjective covering handle them.
The finite index type retains its original arbitrary universe.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.AlgebraicSpace.finite_qc_atlas_assembly`
(node `lem-trf-space-finite-qc-atlas-assembly`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
The final source compiled successfully through `lcompile.py` in 6.7 seconds with no
errors or warnings. Public imports and the theorem statement were compared verbatim
against the original and are unchanged; the maximum Lean line width is 98 characters.

## No longer needed

Removed the following private imports:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `WeilConjectures.Mathlib.CategoryTheory.Yoneda`
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`
- `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`
- `Mathlib.AlgebraicGeometry.Morphisms.Basic`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Mathlib.CategoryTheory.Extensive`

The site, Yoneda, basic morphism, open-immersion and fppf APIs are available through
the existing public imports. Extensive-category coproduct distributivity is unused.
Only the scheme-test module and the three Mathlib proof API imports are needed in
addition to the original public imports.

The proof no longer needs `lem-sc-etale-fibre-product-base-change-coproduct` or
`lem-weil-pbc-etale-covering-composition`. It uses the pullback open cover directly
instead of identifying the full test scheme with a coproduct, and lifts points directly
instead of composing covering families. Both dependencies are removed from the item's
DAG proof; their existing declarations and nodes are preserved.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and no mathematical error was found. The original DAG's
comparison of two families of test schemes is unnecessary: source locality and a direct
pullback lift prove the same properties. No unit statement or realized unit step is
bypassed (`sk-i-curve-zero` has no realized attachment to this node).

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
