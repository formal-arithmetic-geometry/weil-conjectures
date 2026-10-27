## What changed

Filled five proof bodies in `Sheaf.AlgebraicGeometry.CompactProductArrows`.
The two projection identities use the defining pullback lift equations.
`compactProductOpen` uses Mathlib's `Scheme.pullback_map_isOpenImmersion` instance.
The restriction-family and compact-map-family normalization witnesses are constructed
componentwise from the explicit cores already present in the module; their normalization
fields are reflexivity. All six existing imports remain, and no imports are added.
A declaration-local unused-section-variable linter setting preserves the existing
`HasSmallSiteSheafify C` binder of the restriction normalization theorem.
No declaration signature, definition body, instance attribute, or public import changes.

## Proved and sorry left

Closed five of the six original holes:

- `AlgebraicGeometry.Etale.compactProductOpenMap_fst`.
- `AlgebraicGeometry.Etale.compactProductOpenMap_snd`.
- `AlgebraicGeometry.Etale.compactProductOpen`.
- `AlgebraicGeometry.Etale.compactProductRestriction_exists_normalized`.
- `AlgebraicGeometry.Etale.compactProductMap_exists_normalized`.

One original hole remains unchanged:
`AlgebraicGeometry.Etale.compactProductExtension_isIso`
(node `def-pur-compact-product-arrows`).
No holes were added or split off. The map normalization theorem still depends on the
existing extension-isomorphism theorem, as its statement already did.
The first single-file compile passed in 13.0 seconds, with only the unused-section-variable
warning addressed by the local setting above. Delivery verification reruns the compile
and axiom probe on the final file.

## No longer needed

None. No imports, nodes, or modules are pruned. The original node has no proof dependencies,
and the implemented constructions follow its existing statement and declaration docstrings.
All three statement dependencies and the unit route are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or route repair was needed for these five proofs. The source
node has an empty `proof` array; its statement and the declaration docstrings nevertheless
specify these constructions completely, so their route is unchanged.
The remaining generic-coefficient extension-isomorphism hole is not solved by the adopted
`nonempty_iso_derivedTensor_leftDerivedUpperStar_openImmersionLowerShriek`, which is stated
for module coefficients. The adopted generic open projection isomorphism additionally
requires a concrete coefficient category and sheaf-composition hypotheses absent here.
No such hypotheses were added to the statement, and no replacement hole was introduced.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
