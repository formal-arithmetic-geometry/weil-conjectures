## What changed

Proved `WeilConjectures.RationalVerdier.rational_evaluation_detect` in
`Sheaf.SixFunctors.RationalVerdierEvaluationDetection`, with its statement unchanged.
Private helpers construct the integral Hom linear equivalence, identify its value using
completion naturality, and identify its scalar extension with the prescribed rational
pairing by induction on tensors. The only additional project proof import is
`Sheaf.Paper.IntegralDerivedHomBilinear`. The item node records this dependency and
these proof steps. No other existing module or public interface is changed.
The final module compiled through `lcompile.py` without warnings in 13.9 seconds.

## Proved and sorry left

Closed the one existing hole in
`WeilConjectures.RationalVerdier.rational_evaluation_detect`
(node `lem-coef-rational-verdier-evaluation-detection`). No holes added or split off;
no `sorry` remains in the delivered module. All private definitions are explicit
constructions, and all private lemmas are proved.

## No longer needed

No original import or declared dependency is removed. No node or module is withdrawn.
The proof uses the original integral-adjunction and scalar-localization plan directly.
It needs no general rational internal-Hom adjunction, finite scalar-extension
comparison, signed symmetry, or bidual comparison.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The DAG's first step needed the existing
`lem-sf-integral-derived-hom-bilinear` to justify linearity of the ambient right
adjoint; this is now explicit in its proof dependencies. A general rational
internal-Hom adjunction lies downstream of this module and cannot be imported here;
the direct fixed-dualizing-object construction avoids that dependency cycle.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 4 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierEvaluationDetection": "08eb52e1ed950e2634626fcef6b9479cc7ef9bfb"}, "results": {"Sheaf.Paper.SfBidualityClass": {"hash": "3d09b2271a532ea090a93820751ad92e2f041e90", "status": "OK"}, "Sheaf.SixFunctors.RationalDualFormulaAdjunction": {"hash": "fa718e0a302c6ed7933bd5616dfabe953aed0dd0", "status": "OK"}, "Sheaf.SixFunctors.RationalHomAdjunction": {"hash": "4387bdd6689d18fec3408609c9f2d63b036069cf", "status": "OK"}, "Sheaf.SixFunctors.RationalVerdierPairingCalculus": {"hash": "b2ecb41013c0b37a602e6682bb0e28bf16f244cc", "status": "OK"}}, "seconds": 189, "time": "2026-10-28T10:26:26+0800", "transitive": 3, "version": 1}
```

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
