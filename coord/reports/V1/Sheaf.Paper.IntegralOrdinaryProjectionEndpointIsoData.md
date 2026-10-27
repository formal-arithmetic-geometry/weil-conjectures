## What changed

Proved `WeilConjectures.integralOrdinaryProjection_endpointIsoData` in
`Sheaf.Paper.IntegralOrdinaryProjectionEndpointIsoData`, with its signature and the
endpoint data structure unchanged. Added only private, proved comparison helpers and
proof imports. No existing public definition, instance, attribute or import changed.

The construction first identifies the completed ringed pushforward with
`sfCompletedModuleDirectImage`. It reuses the already proved private
`sf_projection_formula` and `sf_projection_map` of `SfCompleteDirectImageReduction`
through `import all`. Unlike that module's final completeness theorem, this auxiliary
projection theorem holds for arbitrary unbounded inputs. The exact open scalar mate
then gives reduction of compact support. Scalar tensor/pullback comparisons and the
finite tensor, pullback and compact-support realization isomorphisms give the two
endpoints. The small derived-category universe of fixed pullback is specified explicitly
in a private abbreviation. All auxiliary constructions are complete Lean terms.

The existing node's proof and proof dependencies now describe these compositions.
No new nodes, public declarations, change records or other existing modules are included.
The module compiled cleanly through `lcompile.py` in 15.9 seconds.
Zero inputs, empty schemes and level zero (positive exponent one) need no extra
hypotheses: all comparisons used apply to arbitrary inputs and morphisms.

Searches: LeanFinder returned eight unrelated cotangent/differential results for the
scalar tensor/direct-image query; Loogle returned generic product `mapIso` results;
Mathlib grep returned zero hits. Repository searches found the existing arbitrary-input
`sf_projection_formula`, which removes the need for any new split.

## Proved and sorry left

Closed one hole: `WeilConjectures.integralOrdinaryProjection_endpointIsoData`
(node `lem-sf-ordinary-projection-endpoint-iso-data-q2`).

The item has zero remaining `sorry`s. Added zero holes and split off zero obligations.
The imported existing scalar-tensor and finite-realization theorems retain their own
independent proof obligations; none was restated or added by this delivery.

## No longer needed

No existing imports were removed; both original public imports occur in the endpoint
statements. The proof does not need these originally planned dependencies:

- `lem-weil-pbc-ringed-exchange-tensor-coherence`
  (`Sheaf.Paper.RingedExchangeTensorCoherence`);
- `lem-sf-open-projection-factor-coefficient-change`
  (`Sheaf.Paper.OpenProjectionFactorCoefficientChange`);
- `lem-sf-projection-scalar-square` (`Sheaf.Paper.ProjectionScalarSquare`);
- `lem-sf-finite-scalar-proper-projection-presentation`
  (`Sheaf.Paper.FiniteScalarProperProjectionPresentation`).

These concern equality of projection arrows or their proper/open factors. Endpoint
existence uses only object comparisons. They are removed from this node's proof
route, not withdrawn from the library or declared unnecessary for other nodes.
The perfect-quotient direct-image result remains used through the existing normalized
arbitrary-input direct-image proof. The unit statement and its proof route are preserved.

## Where the brief, the DAG or earlier work was wrong

The earlier endpoint proof plan mixed the construction of endpoint objects with
commutativity of the projection square. No arrow compatibility theorem is needed
for this item; existing object comparison APIs suffice to close its hole.

STATEMENT-DISPUTED (separate companion item, reported upward):
`WeilConjectures.integralOrdinaryProjection_endpointCompatibility` in
`Sheaf.Paper.IntegralOrdinaryProjectionEndpointCompatibility` quantifies over every
`IntegralOrdinaryProjectionEndpointData`. Its structure contains two arbitrary
isomorphisms and no normalization or compatibility condition. The claimed equation
cannot hold for every such pair: over odd residue characteristic, change only the
source isomorphism by multiplication by -1. For the identity compactification and
nonzero tensor-unit inputs the projection is nonzero and invertible, so the two
compatibility equations would imply that projection equals its negative. For example,
residue field F_3 makes this impossible. The companion statement must refer to a
specified construction or assert existence of compatible endpoints, rather than
universal compatibility of arbitrary endpoints. This delivery proves only the assigned
existence statement and does not alter that separately assigned module.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralOrdinaryProjectionEndpointIsoData": "53ba64f97ae8cc5c91b93471d87afaa774f8befe"}, "results": {"Sheaf.Paper.IntegralOrdinaryProjectionEndpointCompatibility": {"hash": "a6928487525850336f2be911836f452950a2a776", "status": "OK"}}, "seconds": 33, "time": "2026-10-28T06:29:47+0800", "transitive": 0, "version": 1}
```

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
