## What changed

Proved `AlgebraicGeometry.Monoscheme.restrict_smallest_neighborhoods` and
`AlgebraicGeometry.Monoscheme.smallest_neighborhood_realizations_cover` in the assigned module.
The restriction proof constructs the sheafed-space factorization through the target open
immersion, proves germ naturality directly from the actual stalk colimit, and transports
the product splitting in `Hom.IsSmooth` using the canonical germ equivalences. The
covering proof constructs the prime of nonunits, proves every monoid-spectrum point
specializes to it, and shows each affine open equals one of the prescribed smallest
neighborhoods. Mathlib's joint surjectivity of the open-gluing colimit finishes the proof,
including the empty monoscheme.

Added only proved private helpers. Added private proof imports of
`Mathlib.Geometry.RingedSpace.OpenImmersion` and
`Mathlib.CategoryTheory.Limits.Shapes.Terminal`. Updated the assigned node's proof steps
2, 3 and 6 and its proof origin. Existing theorem types and public imports are preserved;
the unused bound variable in the covering family's type is named `_y` to avoid a warning.

## Proved and sorry left

Closed two of the original five holes:

- `AlgebraicGeometry.Monoscheme.restrict_smallest_neighborhoods`.
- `AlgebraicGeometry.Monoscheme.smallest_neighborhood_realizations_cover`.

Added zero holes and zero split statements. Three original holes remain, each attached
to `lem-trf-monoscheme-smooth-local-charts` with its original source and proof docstring:

- `AlgebraicGeometry.Monoscheme.exists_smallest_affine_neighborhood`.
- `AlgebraicGeometry.Monoscheme.affine_smallest_neighborhood_formula`.
- `AlgebraicGeometry.Monoscheme.realized_smallest_product_chart`.

The two completed clauses do not use any of these three remaining statements.
Validation: the assigned module compiled through `lcompile.py` in 6.9 seconds.
The final packet replaces the diagnostic `simp?` with an explicit lemma list and
rewrites the presheaf identity map explicitly. Delivery preflight recompiles this
final version and checks declaration axioms
and the actual remaining-hole inventory.

## No longer needed

Removed private imports `Mathlib.AlgebraicGeometry.OpenImmersion`,
`Mathlib.AlgebraicGeometry.AffineSpace`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`: the completed proofs use
sheafed-space open immersions and open-gluing colimits, and the polynomial/Laurent
smoothness clause remains unchanged.

For the completed restriction clause, the dependency
`lem-trf-fine-monoid-local-smooth-charts` and its recorded module
`Sheaf.AlgebraicGeometry.FineMonoidLocalSmoothCharts` are unnecessary: the stalk splitting
is already the definition of `Hom.IsSmooth`. The dependency stays in the node because
the unfinished smallest-affine-neighborhood clause still plans to use it. No whole node
or module is withdrawn, and no unit statement or route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The recorded proof dependency `Sheaf.AlgebraicGeometry.FineMonoidLocalSmoothCharts` has
no source file in the shared checkout, and no matching quarantine row was found in
`coord/rework.tsv`. This did not obstruct the two completed clauses, which use the
existing definitions directly. The remaining neighborhood/localization clauses still
need the ordinary affine localization interface; it was not recreated or weakened here.

Mathlib's general stalk lemmas assume all small colimits in the value category. This
project supplies only filtered colimits of commutative monoids, so the proof uses the
actual `FineFan.stalkDiagram`, `germ` and `stalkMap` colimit equations instead. The
covering argument does not need finite generation, integrality, or torsion-freeness
beyond the existing theorem's assumptions. All new helpers are proved in Lean.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
