## What changed

Proved `WeilConjectures.IntegralOrdinary.reductionTensorPullback` by transporting the
existing general `IntegralSystemRealization.canonicalReductionTensorPull` square to
this item's specified ordinary models. Its signature and three public imports stay
unchanged. Added proof imports for the normalized model existence theorems, primitive
quotient augmentations and the general square. The proof uses six new supporting modules.

The new modules prove normalized tensor model identification and pullback transport
(`IntegralTensorModelTransport`), equality of the strict tensor chains
(`IntegralTensorChainIdentification`), identification of tensor reduction
(`IntegralTensorReductionIdentification`), and the single-input pullback completion
augmentation identification (`IntegralPullbackAugmentationIdentification`), supported
by the cochain model and derived computation-map identification
(`IntegralPullbackComplexIdentification`) and the actual module adjunction comparison
(`IntegralPullbackModuleIdentification`). These
helpers retain whole strict towers and both Roos cone coordinates. They never infer
equality of derived maps from their separate finite evaluations.

The general canonical square is used as a generic tool from the compatibility unit.
The normalization transport is the missing bridge between that tool and the specified
augmentations here. The item's blueprint unit and its statement are preserved.

## Proved and sorry left

Closed the one original hole, in
`WeilConjectures.IntegralOrdinary.reductionTensorPullback`.
Added zero holes and split off zero `sorry` statements. The item and all new modules
contain zero `sorry` occurrences. All seven new public helper theorems are proved.
The two new isomorphism definitions
`pullbackPushforwardIso` and `pullbackModuleIso` are explicit constructions with no holes.
The proof uses existing declarations, including the still-unproved general
`IntegralSystemRealization.canonicalReductionTensorPull`; this delivery does not claim
to prove that pre-existing dependency.

Validation: `lcompile.py --all` compiled all seven delivered Lean files successfully.
Each file met the 60-second limit; the assigned item compiled in 9.7 seconds.

## No longer needed

No original public import or module was removed or withdrawn. No module is claimed
pruned. Exploratory proof imports of `ProEtaleTensorPullbackDescentData`,
`RingedTensorChainIdentification`, `TensorOperationUnitNormalization`,
`StrictTensorAugmentationNormalization`, and `import all IntegralOperationsWellDefined`
were removed from the item; the supporting modules import the parts they use.
The new tensor-chain helper imports `ConstructibleTensorCompletionChain` directly
instead of the broader `IntegralTensorReductionAugmentation`.

The original direct proof plan's dependencies
`lem-sf-tensor-reduction-augmentation`, `lem-pc-kflat-resolution`,
`lem-pur-coherent-reduction-kflat`, `lem-pur-integral-ambient-operation-models`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-pur-coherent-derived-pullback-tensor`,
`lem-pur-sequence-pullback-tensor-cochain`,
`lem-coef-derived-system-evaluation-calculus`, and
`lem-pur-integral-operations-well-defined` are no longer direct proof dependencies
of this item. Their necessary representative and chain calculations are supplied
through the imported general square and proved normalization helpers. They remain
available, and several remain transitively needed; this is not a request to withdraw
their declarations or modules.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original plan repeated a calculation already
stated by `canonicalReductionTensorPull`. Applying that existing tool requires actual
model identifications; the new proofs supply them, rather than postulating another
copy of the tensor/pullback square. The single-input pullback identification compares
the specified ordinary completion map with the strict quotient augmentation by the
module adjunction, quotient generators, and zero-coordinate mapping-cone formula.

No existing module besides the assigned item, no shared definition, and no existing
public declaration signature or visibility was changed. No change record or forced
adaptation is needed.

## New nodes

`lem-sf-integral-tensor-model-identification`: the normalized isomorphism between two
ordinary tensor presentations, obtained by fully faithful representative restriction.

`lem-sf-integral-tensor-model-pullback-transport`: the canonical tensor pullback square
commutes with any such normalized model isomorphisms, proved on representatives and
transported by faithful restriction.

`lem-sf-integral-tensor-chain-identification`: equality of ringed and constructible
strict tensor augmentation chains by their two-coordinate uniqueness.

`lem-sf-integral-tensor-reduction-identification`: identification of the specified
reduction comparison under a normalized tensor model isomorphism, by its adjunct.

`lem-sf-integral-pullback-augmentation-identification`: equality of the ordinary
single-input pullback completion map with any normalized strict pullback model's unit.

`lem-sf-integral-pullback-complex-identification`: a cochain pullback isomorphism
preserving inverse adjunction-unit sections and the derived computation map. This
proved part was extracted after profiling the concrete derived-factorization kernel
check; it introduces zero holes and keeps each file within the compile limit.

`def-sf-integral-pullback-module-identification`: the actual module pullback
isomorphism, constructed from the direct-ring-map equality and the two adjunctions.
Its data body contains no private helper or postponed construction.

`lem-sf-integral-pullback-module-unit`: the inverse module comparison preserves
adjunction-unit sections. Separating this module-level API from derived functor
coherence gives each file a larger margin below the compile limit.

`def-sf-integral-pullback-pushforward-identification`: the actual direct-image module
isomorphism from equality of the direct ring maps. The pullback construction uses
this public data directly, avoiding a duplicate comparison of two data constructions.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralPullbackAugmentationIdentification": "7a98a2a3b7a80553507911b83b1949c4a7e2910e", "Sheaf.Paper.IntegralPullbackComplexIdentification": "6e872afec4232ef96b5ff665c4d4fc617ccfdadd", "Sheaf.Paper.IntegralPullbackModuleIdentification": "ef54af889cb5867054d13aa6ad65ae229eade27a", "Sheaf.Paper.IntegralReductionTensorPullback": "1bac01241a90163d109b86907d682afbafe27538", "Sheaf.Paper.IntegralTensorChainIdentification": "eb06046f95dde55dee550a2254dd209b68a34eae", "Sheaf.Paper.IntegralTensorModelTransport": "57768cc635f96ac8fe100a6dc137c5d4e8c2716e", "Sheaf.Paper.IntegralTensorReductionIdentification": "76083353d8bdef9c4b6e8cba563180ae3ea3c403"}, "results": {}, "time": "2026-10-28T05:17:43+0800", "transitive": 0, "version": 1}
```

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
