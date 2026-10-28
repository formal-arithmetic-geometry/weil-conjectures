## What changed

Proved `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_kflat_localization_equivalence` by applying the existing `CategoryTheory.rightFractionDenseSubcategory` theorem. The proof supplies the ambient derived quotient, the native K-flat full subcategory, and the restricted quasi-isomorphism inversion hypothesis; it then transports the equivalence supplied by the dense-subcategory theorem to the canonical `Localization.Construction.lift` using the universal lifting isomorphism.

Added `Sheaf.Paper.NativeWeilTensorRingedKFlatResolution`, which records the native K-flat replacement and complex quasi-isomorphism fraction-calculus input needed by the dense-subcategory argument.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_kflat_localization_equivalence`.

Added one named split theorem, still `sorry`:

- `AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_kflat_resolution`, in node `lem-sf-native-weil-tensor-ringed-kflat-resolution`.

This theorem is a strict decomposition: it supplies the native K-flat density and the ambient right calculus of fractions, while the item proves the localization equivalence by real categorical composition. No definition contains a `sorry`.

## No longer needed

No existing module or DAG node is withdrawn. The original item node had no proof dependencies; the proof now uses `lem-trf-right-fraction-dense-subcategory` and the new native replacement theorem. The direct item imports are limited to the statement imports, the dense-subcategory theorem, and the new resolution module. No unused proof-only import remains.

## Where the brief, the DAG or earlier work was wrong

The item’s original DAG proof had an empty dependency list despite requiring the roof-density and fraction-calculus argument. The missing input is now recorded as one named intermediate theorem with the construction and source described in its docstring. The target statement and all existing declarations retain their signatures.

## New nodes

- `lem-sf-native-weil-tensor-ringed-kflat-resolution`: native K-flat replacement density together with the right calculus of fractions for complex quasi-isomorphisms. The corresponding module is `lean/Sheaf/Paper/NativeWeilTensorRingedKFlatResolution.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NativeWeilTensorRingedKFlatLocalizationEquivalence": "5da2d5deaba61149d3da85b2d85badfca92ba76a", "Sheaf.Paper.NativeWeilTensorRingedKFlatResolution": "3b23408693688dc6354fac7d20049e3b9ca36b30"}, "results": {}, "time": "2026-10-28T08:16:59+0800", "transitive": 0, "version": 1}
```

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
