## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.unramified_etale_compatible_charts`
with its signature unchanged. The recognition clause applies the existing presentation
criterion to the two existing scheme-locality statements. The atlas clause uses the
scheme test of the prescribed target atlas, Yoneda full faithfulness, and composition
of representable étale and surjective maps. Three proved private helpers handle
independence of scheme tests, scheme-map tests, and surjective composition.

Removed the redundant private import of
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`; added the private
proof import `Mathlib.CategoryTheory.Limits.Yoneda`. Public imports are unchanged.
Updated the item's DAG proof to describe the actual scheme-test argument.

Validation: the remote single-file compile passed in 3.1 seconds with no warnings.
The delivery preflight checks the final file and its declaration axioms.

## Proved and sorry left

Closed the single original hole in
`AlgebraicGeometry.AlgebraicSpace.unramified_etale_compatible_charts`
(node `lem-sfb-unramified-etale-compatible-charts`). No holes added or split off.
No `sorry` remains in this delivery. The proof uses the existing stated theorems
`scheme_unramified_etale_locality`, `scheme_etale_source_target_properties`, and
`etalePresentation_property_criterion`; their independent proof obligations remain
in their owning modules.

## No longer needed

Removed the direct private import of
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers` and the proof dependency
`lem-trf-space-fibre-products-etale-covers`, including its top-level `tool_uses` entry.
The atlas is represented directly by the scheme-test hypothesis, so none of that
module's three theorems is used. The module remains transitively imported through the
unchanged public morphism-properties module; this delivery does not withdraw it or
claim that it is globally pruned. All other declared original proof dependencies are
retained. The unit route is unchanged; the unit's realized lists are empty.

## Where the brief, the DAG or earlier work was wrong

The original argument is valid, but invoking algebraic-space fibre products is
unnecessary for the atlas construction: the definition of representable étaleness
already supplies the required scheme and pullback square. Étaleness and surjectivity
may initially give different representing schemes, so surjectivity must be transported
across their unique isomorphism; this is now explicit. The two existing locality
statements order the final existential binders differently, so the proof reorders them.
Empty cases require no separate construction, since no point is chosen.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
