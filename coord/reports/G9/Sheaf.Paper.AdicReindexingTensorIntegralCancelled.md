## What changed

Replaced the body of `normalized_reindexing_tensor_integral_cancelled` by a diagram
calculation. Its signature and its original public import are unchanged. Two proved
coordinate lemmas extract exactly the finite tensor and integral pullback coordinate
identities from `FiniteNormalization.integral_tensor` and
`integralRealizationAgreement`. Naturality of the inverse comparison, of the target
integral realization, and of the two tensorators then pastes the two lower squares.
The proof cancels only an explicitly invertible coordinate map and appends the target
inverse tensorator at the end.

Added `AdicIntegralTensorCoordinates`, containing four explicit composites of the
existing maps, `AdicIntegralRealizationCoordinates`, which gives the existing
integral realization comparison an explicit coordinate type, and the two theorem modules
`AdicFiniteIntegralTensorReindexing` and
`AdicIntegralStagePullTensor`. The proved general pasting calculation is in
`AdicIntegralTensorPasting`. No arbitrary witness or data from an unproved existence
theorem is chosen. All changes are confined to the item, new modules, and their nodes.

All six modules compiled in import order through `lcompile.py --all`; the largest
file took 47.9 seconds and the item took 31.9 seconds. Profiling options used to
diagnose elaboration have been removed before delivery.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.AdicQbarRealization.normalized_reindexing_tensor_integral_cancelled`.
The item has no remaining holes. The lemmas `finite_tensor_coordinates`,
`integral_pull_coordinates` and `pasteIntegralTensorSquare`, and the private helper
`inverse_coordinates`, are proved. The five coordinate definitions contain no holes.

Added two holes, so this delivery is a decomposition, not a net reduction of holes:

- `WeilConjectures.AdicQbarRealization.finite_integral_tensor_reindexing`
  (`lem-sf-adic-finite-integral-tensor-reindexing`). This is the square in ordinary
  derived module categories before raw rationalization or common-stage inclusion.
  It has no `FamilyCore`, no common-stage comparison, and no integral realization
  agreement hypothesis. It uses just the finite representative and quotient-completion
  normalization and the ordinary scalar and tensor reindexing data.
- `WeilConjectures.AdicQbarRealization.integral_stage_pull_tensor`
  (`lem-sf-adic-integral-stage-pull-tensor`). This is solely the coefficient-operation
  transport equation, with no native realization, finite scalar tensorator, or
  reindexing comparison. It applies to arbitrary scheme morphisms with the stated
  residue-field invertibility. It is independent of the ordinary scalar square.

Each hole is exactly a public theorem proved by `by sorry`, with its own module,
node, source and full proof in words. The equations handle zero inputs, empty schemes,
and torsion integral objects; neither assumes a faithful rationalization or a tensor
product of bounded finite-coefficient objects to be bounded.

## No longer needed

No module is withdrawn and no existing import is removed. No global pruning is
claimed. The original planned uses of `lem-fix-constructible-tensor-completion`,
`lem-pur-cochain-pullback-tensor-coherence` and `lem-pur-derived-pullback-tensor-iso`
are now lower dependencies of the finite scalar square, rather than direct steps of
the item's proof. They remain necessary there. The coefficient-stage transport is
recorded separately instead of being hidden in the phrase "descend through raw
rationalization and inclusion". The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The former node bundled the finite ordinary representative calculation with the
independent coefficient-operation transport. Generic cancellation only recovers the
parent theorem, so it cannot prove this item. The new proof makes the separation
explicit and implements the intervening naturality and cancellation argument.
Neither new theorem is the original statement renamed or with a repackaged hypothesis:
one identifies maps in finite ordinary coefficient categories; the other identifies
the published coefficient operations before realization. They combine by a genuine diagram calculation.

Searches through the existing native normalization modules and the adopted source
library found no existing theorem for either lower square. Mathlib searches using
LeanSearch, LeanFinder, Loogle and grep returned generic naturality, monoidal functor
and tensor transport lemmas, rather than these native comparison equations. Exact
queries and search results are recorded in the new nodes and searches.jsonl.

## New nodes

`def-sf-adic-integral-tensor-coordinates`, module
`Sheaf.Paper.AdicIntegralTensorCoordinates`, records `finiteIntegralTensorMap`,
`finiteIntegralPullMap`, `integralStagePullIso` and `integralStageTensorIso`. All are
explicit composites of existing maps; `tensorStage`, the existing definition of
raw rationalization followed by inclusion, is reused.

`def-sf-adic-integral-realization-coordinates`, module
`Sheaf.Paper.AdicIntegralRealizationCoordinates`, records the typed abbreviation
`integralCoordinateIso` for the existing integral realization isomorphism and the
proved normalization consequences `finite_tensor_coordinates` and
`integral_pull_coordinates`.

`lem-sf-adic-integral-tensor-pasting`, module
`Sheaf.Paper.AdicIntegralTensorPasting`, is a proved diagram lemma for arbitrary
categories. Separating these proved calculations keeps each Lean file within the
compile limit; it adds no hole.

`lem-sf-adic-finite-integral-tensor-reindexing`, module
`Sheaf.Paper.AdicFiniteIntegralTensorReindexing`, is the finite ordinary scalar square,
proved in words from K-flat pure-section and full quotient-completion coordinates.

`lem-sf-adic-integral-stage-pull-tensor`, module
`Sheaf.Paper.AdicIntegralStagePullTensor`, records the transport of the canonical
integral comparison through raw rationalization and common-stage inclusion, with all
literal object identifications retained. No existing statement or definition changed,
so there is no change record or forced adaptation.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicFiniteIntegralTensorReindexing": "e3c199569f00de39373e39f5de40f0b1b8c540c9", "Sheaf.Paper.AdicIntegralRealizationCoordinates": "3466680c99958c4d37115659840ec389e5c95709", "Sheaf.Paper.AdicIntegralStagePullTensor": "29d76fc2511977f89567ef90f337c6dcb9ba1434", "Sheaf.Paper.AdicIntegralTensorCoordinates": "132d25d5e1912cc653b866dfa69632fce66f0c25", "Sheaf.Paper.AdicIntegralTensorPasting": "05b4ed8e9baf449026083b4d393c558548604b86", "Sheaf.Paper.AdicReindexingTensorIntegralCancelled": "31a5ef3e5481dff6bdf7f1d388ff2e4a30357fb3"}, "results": {"Sheaf.Paper.AdicReindexingTensorIntegral": {"hash": "5a526b1b502c78c399d3f393f04b2c647e58a2ca", "status": "OK"}}, "seconds": 107, "time": "2026-10-28T12:32:09+0800", "transitive": 0, "version": 1}
```

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
