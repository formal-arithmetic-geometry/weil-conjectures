## What changed

Proved `WeilConjectures.commonFrobeniusSquare_eq` in the assigned module, keeping its
statement and both public imports unchanged. Added six proved `Sheaf.Paper.CommonStage*` helper modules and proof imports for their
interfaces, plus private access to Mathlib’s small-type implementation used by coefficient
stages. The target statement and its two public imports are unchanged.

The argument first derives the rational coefficient-unit equation from the existing
scalar tower law. It compares each common-stage compositor at the object's original
coefficient stage, where the three unit comparisons cancel by rational naturality.
Both compositors thus equal the same localized integral map. Their Frobenius-square
composites agree, including the middle equality transport.

## Proved and sorry left

Closed the one original hole: `WeilConjectures.commonFrobeniusSquare_eq`
(node `lem-pur-common-frobenius-square-normalization`). Added zero holes; split off zero
statements. The proof is factored into six proved helper modules (all with zero holes) for
coefficient-unit normalization, rational naturality, generic normalized composition, the
literal-stage word, its representative, and integral normalization. No `sorry` remains in the delivered module. Existing imported proof
obligations are used through their recorded declarations, as intended by stage 3.

## No longer needed

The target no longer imports `Sheaf.Paper.RationalPullbackScalarTower` directly; that proof import
now belongs to `CommonStagePullbackCoefficientUnit`. No modules are withdrawn or pruned. The theorem `derivedPullbackTensorIso` and its node `lem-pur-derived-pullback-tensor-iso` are
not needed by the proof: the imported compositor declarations from
`DerivedPullbackTensorConstraints` suffice. The unit route and the original statement
dependencies remain unchanged.
No separate scalar/composition compatibility lemma or enlargement of a coefficient
field is needed: coefficient-unit normalization at the original stage suffices.
The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The planned assertion that the two normalizations agree hid the coefficient-unit
calculation: a stage's reflexive transition is not definitionally the identity.
The proof now derives and retains its actual unitor instead of assuming it away.
The current server queue lists this as a one-hole proof item. Its historical build
error reports a bad `WeilIndSheafCategory` import; the three relevant dependency
sources on the server match the shared snapshot. No dependency interface repair is
needed for the proof.

## New nodes

Added the proved nodes `lem-pur-common-stage-pullback-coefficient-unit`,
`lem-pur-common-stage-rational-composition-naturality`,
`lem-pur-common-stage-normalized-composition`, `lem-pur-common-stage-compositor-word`,
`lem-pur-common-stage-compositor-representative`, and
`lem-pur-common-stage-compositor-integral-normalization`, each matching its new
`Sheaf.Paper.CommonStage*` module and carrying no `sorry`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CommonFrobeniusSquareNormalization": "379ba1dc3c9ea1c15553e510536597798fe15536", "Sheaf.Paper.CommonStageCompositorIntegralNormalization": "745d65f1b68344e45b623d84221885a608215d44", "Sheaf.Paper.CommonStageCompositorRepresentative": "3fd98161cbb4fab422191dae697c57b59c56fff0", "Sheaf.Paper.CommonStageCompositorWord": "4985ebb1fa8d4a49becb163eb5484b8fed748e98", "Sheaf.Paper.CommonStageNormalizedComposition": "9e28eb631312fe093148d0bd328b6714174aae7d", "Sheaf.Paper.CommonStagePullbackCoefficientUnit": "c9476841686af2d6ec0a125ecdbf1314e23e26f1", "Sheaf.Paper.CommonStageRationalCompositionNaturality": "1d5140cd42012d563faa3c4e2b1ad8aa7a9b521b"}, "results": {"Sheaf.Paper.ConstantPurityFrobeniusSquare": {"hash": "57e1afb9cc6da75a28f05ec3856b5b1c77ee5d7b", "status": "OK"}}, "seconds": 56, "time": "2026-10-28T08:55:57+0800", "transitive": 0, "version": 1}
```

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
