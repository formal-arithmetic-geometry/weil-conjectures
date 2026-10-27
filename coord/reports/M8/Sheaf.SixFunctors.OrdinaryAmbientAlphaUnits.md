## What changed

Filled `AlgebraicGeometry.ProEtale.AmbientProperOpen.ordinaryAmbientAlphaUnits` using the
ordinary identity-square clause of `ambientUnderivedClopenPasting`. Private helpers express
both identity words as exact-derived pasting expressions, identify the localized open identity
by its adjunction unit, and cancel the total/exact pullback comparisons. The horizontal
calculation also uses naturality of those comparisons.

Added private proof imports of `AmbientUnderivedClopenPasting`,
`AmbientOrdinaryClopenLocalization` (including its private adjunction-normalization helpers),
and `ExactDerivedTransformationPasting`. The existing statement, public imports and shared
definitions are unchanged. Removed the item's local irreducibility marking of the ordinary
record so its projections can be compared explicitly during these proofs; the large imported
functors retain their local irreducibility markings. Updated the item's node to record the
actual proof route.
No existing consumer needs adaptation.

Validation: the delivered Lean module compiled through `lcompile.py` in 29.8 seconds,
with no errors or warnings. The public theorem signature and existing public import were
checked against the source and are unchanged.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.AmbientProperOpen.ordinaryAmbientAlphaUnits`
(node `lem-sf-ordinary-ambient-alpha-units`), proving both conjuncts.

Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module. All added helpers
are private theorems with complete proofs. No new statement module or axiom was introduced.

## No longer needed

No existing import was removed and no module is withdrawn. The direct planned dependency
`lem-sf-ambient-exact-clopen-comparison-localization` is replaced by the narrower, already
proved `lem-sf-ambient-ordinary-clopen-localization`: only `ordinary_alpha_localized` and the
ordinary exact-adjunction normalization are needed here. The larger comparison module remains
a dependency of `AmbientUnderivedClopenPasting`, so this does not claim global pruning of it.
The simultaneous-system and proper-mate clauses of that larger theorem are not used here.

The item's unit `sk-rem-sf-pf-done` has no realized statement or steps, and its route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original statement and mathematical plan were usable. The remaining localization glue can
be proved with the existing exact-derived-expression API and private normalization helpers;
no further split of the obligation is necessary. Identity opens, empty schemes and zero objects
need no exceptions. No statement or definition repair was needed.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
