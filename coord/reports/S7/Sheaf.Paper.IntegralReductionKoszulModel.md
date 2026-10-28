## What changed

Proved `WeilConjectures.IntegralHom.integralReductionTower_koszul_model` in the assigned
module, preserving its signature and its two public imports. Added private proof imports
and proved private helpers for the localized tensor-tower functor, its inversion of
quasi-isomorphisms, derived representative transport, the K-flat tensor augmentation,
and the comparison with the actual reduction transitions.

The proof reuses the proved augmentation, boundedness and flatness helpers of
`PrincipalKoszulStrictReplacement`, the ordinary `scalarTowerIso` underlying
`FiniteReductionScalarNormalization`, and `integralTowerTransition_eq`. These are read
through private `import all` imports. The coefficient augmentation is tensored directly
with the given K-flat P, using signed symmetry; no second resolution is constructed.
The whole Koszul tensor tower descends by `Localization.lift` and `Localization.fac`,
so the given derived isomorphism changes its representative without choosing a complex
from an unproved existence statement. Updated the item's DAG proof and dependency list.

Validation: the completed module compiled cleanly with `lcompile.py` in 38.3 seconds,
within the 60-second file limit and without warnings.

All writes are confined to this item sandbox. No other existing module or node changes.
The finite-free coefficient argument is unchanged at the unit level. The zero complex,
empty site, and n=0 (exponent one) introduce no extra assumption.

## Proved and sorry left

Closed 1 hole: `WeilConjectures.IntegralHom.integralReductionTower_koszul_model`
(node `lem-sf-integral-reduction-koszul-model`). Added 0 holes; 0 holes remain in the item.
All five private helpers have complete proofs or explicit functor constructions.
This is a proof, with no split-off statement or new node.

## No longer needed

No original import is removed and no module is withdrawn. The planned refinement via
`lem-pc-kflat-resolution` / `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
is not needed in this proof: the supplied P is already K-flat. Removed that proof-dependency
edge. This does not claim that the resolution module is unused elsewhere in the library.
The remaining original dependencies are used for their existing proved helpers.

## Where the brief, the DAG or earlier work was wrong

The original plan imposed flat terms by taking another resolution. Flat terms are needed
for its additional flatness conclusions, but the augmentation quasi-isomorphism after
tensoring only needs K-flatness of P. The already-proved scalar tower construction is
also defined on arbitrary complexes, beyond the good-complex domain of its public theorem.
Using those constructions closes the obligation without a fifth decomposition.

Searches were run through `msearch.py` (LeanFinder, Loogle, and Mathlib grep). They identify
`Localization.lift` and `Localization.fac` as the general descent API; no existing Mathlib
theorem states this completed-coefficient tower comparison. The source library and the
stated dependencies were read before writing the proof.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralReductionKoszulModel": "7c26e47508c948fe09aad723b32646e980d8b726"}, "results": {"Sheaf.Paper.IntegralHomReductionTowerTensorModels": {"hash": "15b4489325348c7337cfcba8e3a5585e0b42a81b", "status": "OK"}}, "seconds": 127, "time": "2026-10-28T12:04:13+0800", "transitive": 0, "version": 1}
```

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
