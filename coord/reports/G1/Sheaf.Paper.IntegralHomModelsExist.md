## What changed

`models_exist` is now proved by combining two strictly smaller proof-plan statements. The new
`Sheaf.Paper.IntegralHomTensorPresentation` module states existence of the source tensor
presentation, and `Sheaf.Paper.IntegralHomReductionPresentation` states existence of one
normalized reduction presentation at a fixed level. The item imports those two proof modules;
their imports expose the K-flat tensor, closed derived, scalar-adjunction, and tensor-pullback
interfaces used by the corresponding proof steps.

## Proved and sorry left

The item theorem `WeilConjectures.IntegralHom.models_exist` is proved with zero `sorry`s left
in the item module. Two strictly simpler intermediate statements remain as named sorries:
`WeilConjectures.IntegralHom.tensor_presentation_exists` (node
`lem-sf-integral-hom-models-exist-tensor`) and
`WeilConjectures.IntegralHom.reduction_presentation_exists_at` (node
`lem-sf-integral-hom-models-exist-reduction`). No definitions contain `sorry`.

## No longer needed

The item module no longer imports `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`,
`Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`,
`Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`,
`Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`,
`Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`,
`Sheaf.Paper.ProEtaleCanonicalTensorPullback`, or
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` directly. They remain
proof-only imports of the new tensor intermediate where required by its recorded route. The
parent node's original three proof steps are replaced by the two new nodes; no other declared
DAG dependency is used by the combining proof.

## Where the brief, the DAG or earlier work was wrong

The nearest existing theorem `integralHom_presentation_evaluation` is restricted to one
universe for the scheme, finite-field datum, and coefficient field. It cannot be instantiated
for this item's independent universes `d`, `t`, and `u`, so it does not prove this statement.
The original DAG proof is mathematically the same route but leaves the tensor construction and
the fixed-level coefficient construction fused into one unproved existential. They are split
here at that boundary.

## New nodes

`lem-sf-integral-hom-models-exist-tensor` records the normalized source tensor construction
and is implemented by `Sheaf.Paper.IntegralHomTensorPresentation`.

`lem-sf-integral-hom-models-exist-reduction` records one normalized coefficient reduction
construction for a fixed `n` and is implemented by
`Sheaf.Paper.IntegralHomReductionPresentation`.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.Paper.IntegralHomModelsExist": "0b8abf2fceaad79febc3ab025a333a597e4ccdd3", "Sheaf.Paper.IntegralHomReductionPresentation": "7b933b56b52f6528334c8864e5d36928b9579fe7", "Sheaf.Paper.IntegralHomTensorPresentation": "1af7a2f33d250dd72674cae4792435dcc395d886"}, "results": {"Sheaf.Paper.IntegralHomReduction": {"hash": "a2d05524c834750b5f29348b20ab0cc22d6bce8d", "status": "OK"}, "Sheaf.Paper.IntegralHomReductionTowerComponents": {"hash": "a873597aeba586a978fa66fb6aa048677721041e", "status": "OK"}, "Sheaf.SixFunctors.IntegralVerdierSignedCalculus": {"hash": "ed1dbd048bd09c9547ed901e651607feaf98119e", "status": "OK"}}, "seconds": 37, "time": "2026-10-28T06:56:10+0800", "transitive": 0, "version": 1}
```

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
