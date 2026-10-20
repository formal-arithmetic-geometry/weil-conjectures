## What changed

Proved `AlgebraicGeometry.Etale.supportedProductLocalization_naturality` without changing its
signature, the supported exterior product, or any of the normalized comparisons. The proof
pulls the naturality of each supported adjunction counit through the exact pullback comparison,
uses the existing naturality clause of `exists_unique_supportedCoefficientTensorDerived`,
applies derived-tensor bifunctoriality, and transposes with the supported derived adjunction.
Three private categorical helpers are fully proved. The argument implements the coefficient
naturality part of the existing DAG route, so the node's dependency plan stays unchanged.

The final module compiles on the server without warnings. An additional `#print axioms` check
shows `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`: the proof still rests on the
existing stated dependencies, including the normalized coefficient tensor comparison. The
printing command was removed from the delivered source. The full delivery axiom probe also
passes in 12.7 seconds and reports precisely the five original remaining holes. Generic
categorical helpers keep the proof from generating expensive equation lemmas for the
specialized derived-category constructions; no timeout setting or definition was changed.

## Proved and sorry left

Closed one of the six original holes:
`AlgebraicGeometry.Etale.supportedProductLocalization_naturality`.

No holes added or split off. Five original holes remain, unchanged:

- `AlgebraicGeometry.Etale.supportedProductLocalizationFirst`
- `AlgebraicGeometry.Etale.supportedProductLocalizationSecond`
- `AlgebraicGeometry.Etale.supportedProductLocalization_openFirst`
- `AlgebraicGeometry.Etale.supportedProductLocalization_openSecond`
- `AlgebraicGeometry.Etale.supportedProductLocalization_openRows`

## No longer needed

None. No imports, modules, or nodes are withdrawn. The remaining triangle, open-restriction,
and open-row proofs retain their original dependencies and complete natural-language plans.
The coefficient naturality proof needs only the already available supported coefficient
adjunctions and normalized tensor comparison; it needs no new lemma module or import.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was corrected. The existing derived coefficient tensor comparison
already includes naturality in both coefficient modules, so no further chain-level naturality
lemma is needed for `supportedProductLocalization_naturality`.

The remaining five statements require additional comparisons of their specified maps with the
coefficient-Hom triangles, or the ordinary support sequences after open pullback. In particular,
`ExternalRHom.external_rhom_cone_pairing` supplies coefficient-cone compatibility but does not
itself identify those triangles and pairings with `normalizedSupportTriangle` and
`supportedExteriorProduct`. The imported `rightDerivedTrianglePullback` is stated on D+,
whereas `supportedProductLocalization_openRows` is stated for arbitrary unbounded objects.
These are proof obligations, not tool failures; their original holes have not been relocated.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
