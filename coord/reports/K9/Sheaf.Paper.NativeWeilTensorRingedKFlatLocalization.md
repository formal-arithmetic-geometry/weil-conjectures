## What changed

Filled `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_kflat_localization`.
The proof explicitly constructs the localization inverting field for restricted
quasi-isomorphisms and supplies its equivalence field from the new
`NativeWeilTensorRingedKFlatLocalizationEquivalence` module. Removed the unused
`KFlatResolutionIndependentCoefficients` and derived shift proof imports.

## Proved and sorry left

The target theorem
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_kflat_localization`
is proved. One strictly smaller roof/common-refinement theorem remains as a named
split: `native_weil_tensor_ringed_kflat_localization_equivalence` in
`Sheaf.Paper.NativeWeilTensorRingedKFlatLocalizationEquivalence` (blueprint node
`lem-sf-native-weil-tensor-ringed-kflat-localization-equivalence`).

## No longer needed

The proof does not use the former `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
proof import or `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`; no
other declared dependencies are pruned.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the inverting and equivalence fields of
`Functor.IsLocalization` into one large proof. The inverting field is immediate
from the ambient derived-category localization, while the roof and common-refinement
argument is the independent equivalence field. The DAG now records that field as a
separate strictly smaller node.

## New nodes

`lem-sf-native-weil-tensor-ringed-kflat-localization-equivalence` is stated in
`lean/Sheaf/Paper/NativeWeilTensorRingedKFlatLocalizationEquivalence.lean`; its
proof is split off with the source and argument recorded in its docstring and DAG
node. No change record is needed because no existing declaration or definition was
changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeWeilTensorRingedKFlatLocalization": "856bd0112f7c745f24a663d54440975436be0e4a", "Sheaf.Paper.NativeWeilTensorRingedKFlatLocalizationEquivalence": "d0de458543ca2699a92e9e92461d3ff3dd3ff380"}, "results": {"Sheaf.Paper.NativeWeilTensorRingedKFlatData": {"hash": "1fa1cdc7b7fa69f856d5048456ed076934393353", "status": "OK"}}, "seconds": 19, "time": "2026-10-28T05:25:42+0800", "transitive": 0, "version": 1}
```

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
