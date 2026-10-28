## What changed

Replaced `native_proper_projection_models` by a Lean assembly of the actual geometric-fiber proper realization, its source and target section presentations, normalized adjunction models and balanced tensor models. The original theorem signature and `NativeProperProjectionModels` structure are unchanged. The proved private helper `properSectionCochain_isKInjective` supplies the K-injective preservation field using the composite of exact IsoAlgebra forgetting and the section equivalence.

Added `Sheaf.Paper.NativeProperSectionAdjunctionModels` for the sheaf/derived direct-image representative and counit equations (original proof steps 2–3), and `Sheaf.Paper.NativeProperSectionTensorModels` for the normalized total tensor and pullback tensor square (original step 4). The item imports these proof modules privately, together with the generic IsoAlgebra and functor-composition K-injective preservation instances. No existing module besides the item is changed. All three modules have passed single-file compilation through `lcompile.py`; factoring the private helper reduced the item compile from 58.5 to 44.6 seconds.

## Proved and sorry left

Closed the original body hole of `AlgebraicGeometry.ProEtaleWeilSheaf.native_proper_projection_models` by reduction to two strictly smaller steps. This is a decomposition, not an unconditional proof: one original hole closed, two holes added, zero holes remaining in the item module.

The new holes are `AlgebraicGeometry.ProEtaleWeilSheaf.native_proper_section_adjunction_models` (node `lem-sf-native-proper-section-adjunction-models`) and `AlgebraicGeometry.ProEtaleWeilSheaf.native_proper_section_tensor_models` (node `lem-sf-native-proper-section-tensor-models`). Each has a source, a complete proof in words, and its own module and DAG node. There are no holes in definitions or private helpers.

## No longer needed

None. The existing proof route is retained. Its adjunction and tensor dependency lists are attached to the corresponding smaller nodes rather than discarded. No module or unit route is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical error established. The original dependency declarations supply general fixed-pair derived comparisons and ringed tensor machinery, but do not directly state the required normalization in the native section coordinates. The two new statements isolate precisely that translation, while the original theorem constructs the finite-field datum, applies the existing proper realization theorem and proves preservation of K-injectives.

## New nodes

`lem-sf-native-proper-section-adjunction-models` states the inverse/direct-image comparison with identity on sections, its K-injective representative equation, and its derived counit square. It omits the realization-family construction and all tensor assertions.

`lem-sf-native-proper-section-tensor-models` takes fixed realization, coefficient, tensor and normalized adjunction data and constructs the section tensors, balanced native tensor pullback, and their commuting square. Its adjunction input fixes pull by the normalized push and counit; it does not permit an independently rescaled pull comparison. Zero objects, empty schemes and identity maps use the same formulas.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeProperProjectionModels": "372f0d9b83f4227fbec1fa7a352dd3e73d93d61d", "Sheaf.Paper.NativeProperSectionAdjunctionModels": "1e183bc1b3f0d47cc2e92cdb784109cd65277c85", "Sheaf.Paper.NativeProperSectionTensorModels": "64e479cac10835a4506c0a46259f2a50374915c2"}, "own_failed": ["Sheaf.Paper.NativeProperProjectionModels"], "results": {}, "time": "2026-10-28T12:20:44+0800", "transitive": 0, "version": 1}
```

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
