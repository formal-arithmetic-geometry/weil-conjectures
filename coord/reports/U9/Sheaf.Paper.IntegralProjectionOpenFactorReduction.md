## What changed

Kept the signature and both public imports of
`Sheaf.Paper.IntegralProjectionOpenFactorReduction` unchanged. Added proof imports of
`IntegralProjectionOpenTensorCoordinates` and `IntegralProjectionSupportFactorCoordinates`.
The item now combines the two local calculations by actual direct-image mate naturality,
functoriality, and a proved factorization of `ProjectionFactors.second`.
`IntegralProjectionLocalFactors` constructs the two local arrows generically and proves
`ProjectionFactors.second_via_openMap`, keeping the repeated input equality transports out
of the large geometric statements.

Four private helpers and one generic factorization supply the glue without new assumptions:
functoriality of pasting and naturality of the explicit completed-pullback reduction, its transport to the datum proper pullback, naturality of the
proper direct-image coefficient mate (by the proper adjunction Hom bijection and counit
naturality), and the factorization of `second` after moving the input equality transport
through the support identification. The main proof pushes the local open square through
proper image, uses mate naturality, substitutes the one-input support comparison, and
combines the two integral arrows into the original `second`.

The two residual statements separate independent parts of the original argument. The open
square is an equality on the intermediate compactification scheme, BEFORE proper image;
it has no support functor or support comparison. The support square has ONE arbitrary
constructible input and contains no tensor, projection formula, or pullback compositor.
Neither is the original theorem renamed or conjugated. Their definitions of the intermediate
arrows are explicit composites of the already specified maps; no data is chosen from an
unproved existence theorem.

Only the item, the three new modules, their nodes, and the item node are changed. No shared
interface, target, source-library declaration, existing public import, attribute, or instance
is changed. The unit `sk-rem-sf-pf-done` has empty realized statement and step records;
no unit route is bypassed.

## Proved and sorry left

Closed the original textual hole in
`WeilConjectures.FixProjectionCompactification.integralProjectionOpenFactorReduction`
(node `lem-sf-integral-projection-open-factor-reduction`) by a complete assembly.
The item has zero holes, from one before this delivery.

The private `map_paste`, `pullReduction_naturality`,
`properPullReduction_naturality`, and `directReduction_naturality` are proved.
The public `ProjectionFactors.second_via_openMap` is proved in the new definition
node `def-sf-integral-projection-local-factors`.

Added two public whole-proof holes:

- `WeilConjectures.FixProjectionCompactification.integralProjectionOpenTensorCoordinates`
  (node `lem-sf-integral-projection-open-tensor-coordinates`).
- `WeilConjectures.FixProjectionCompactification.integralProjectionSupportFactorCoordinates`
  (node `lem-sf-integral-projection-support-factor-coordinates`).

This is a decomposition, one upper hole closed and two strictly smaller holes added,
net minus one. It is not a proof free of unresolved dependencies. The four private helpers, generic
factorization, and assembly introduce no further holes. Every new definition-bearing term has an
explicit composite body. The remaining public theorems carry the source and a complete
natural-language argument in their docstrings and nodes.

Validation uses only the required remote lcompile.py and deliver3.py pipeline. Compile
results and final mechanical checks are recorded by those tools. All four modules
passed lcompile; the remaining profiler options were removed before delivery.

## No longer needed

No import is removed and no module is withdrawn. There is no global pruning claim.

The parent now uses the two local coordinate statements, the existing coordinate and factor
data, and the operation-stage normalizations needed for naturality. Its former direct uses
of `lem-sf-generator-reduction-coherence` and `lem-coef-integral-residue-tor` move to the local
statements, where their substantive calculations are needed.

The old planned uses of `lem-sf-integral-open-reduction-comparison` (module
`Sheaf.SixFunctors.IntegralOpenReductionComparison`) and
`lem-cbc-completed-extension-zero-comparison` (module
`Sheaf.Paper.CompletedOpenExchangeTransport`) are unnecessary for this argument.
The already proved `lem-sf-open-reconstruction-effectivity` applies to the SUPPLIED
`o` and `z.realizationModel` and gives both invertibility facts directly. This avoids
changing to existentially supplied operations or invoking open base change solely
for completeness. Their removal is from this proof route; no global module pruning
is claimed, since other imports and consumers still use these modules.

`IntegralSupportReductionNormalization` was inspected but is not imported: it states
invertibility and refinement compatibility of supportReduction, not its factorization
through the actual direct-image mate and open coefficient map. The existential arrow
isomorphism of `IntegralProjectionOperationPresentation` cannot identify the fixed endpoint
coordinates and is not imported. No unrelated projection, exchange, or refinement lemma
is introduced. `StrictReductionCompactSupportNormalization` concerns strict adic
quotient exchange, and `CompactSupportRealizationFactorNormalization` concerns the
ordinary ringed proper/open word; neither states the comparison for the fixed
`SixFunctorOperationDatum` support identification, so neither is imported.

## Where the brief, the DAG or earlier work was wrong

The original plan combines two different calculations in its second step: compatibility
of the open tensor/compositor with reduction, and identification of the target support
coordinate. The existing generator coherence theorem is in ordinary/completed expression
coordinates. It does not directly identify the datum's normalized support comparison with
`Coordinates.supportReduction`. Likewise the already stated integral open reduction theorem
has existentially supplied operation models, whereas this item receives the fixed `o` and
`z`. Consequently applying either declaration alone cannot close the original equality.

The reduction keeps both original calculations and makes their interface explicit.
The direct-image mate naturality and the equality transports in `second` are proved in Lean,
rather than postponed. New statements were checked mathematically on zero inputs, identity
opens, empty opens, and identity compactifications: they retain actual units, counits and
quotient augmentations in those cases. No finite-evaluation faithfulness is assumed.

Searches through msearch LeanFinder, Loogle, LeanSearch and Mathlib grep found generic
adjunction and scalar-extension tools, but no theorem about these normalized geometric
endpoint maps. Local library and blueprint searches found no duplicate of either local
statement. The Mathlib Hom naturality identities are used for the direct mate calculation.

## New nodes

`lem-sf-integral-projection-open-tensor-coordinates`, module
`Sheaf.Paper.IntegralProjectionOpenTensorCoordinates`, isolates the open tensor and inverse
pullback-compositor square before applying proper image. It removes all support and proper
image comparison work from that task.

`lem-sf-integral-projection-support-factor-coordinates`, module
`Sheaf.Paper.IntegralProjectionSupportFactorCoordinates`, identifies the one-input support
coordinate with the paste of the direct-image mate and open reduction. It removes all
tensor, projection and pullback-compositor work from that task.

`def-sf-integral-projection-local-factors`, module
`Sheaf.Paper.IntegralProjectionLocalFactors`, constructs `ProjectionFactors.openMap` and
`ProjectionFactors.supportMap` as actual composites and proves their factorization
`ProjectionFactors.second_via_openMap` in arbitrary supplied coefficient categories. It
adds no hole.

No change record is needed: existing signatures, definitions, instances, attributes, and
public imports are unchanged. New public statements live only under Sheaf.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
