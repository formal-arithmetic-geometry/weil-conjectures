## What changed

The target module now packages the reversed exactness proposition from two named
intermediate statements. `EtaleHomTransposeExactShiftData` states the normalized
shift structures, component equations, and triangulated functors. The
`EtaleHomTransposeExactCommShift` module states the remaining shift compatibility
of the evaluation transpose. Both intermediate proofs are left as named stage-3
holes with source and proof descriptions; the target proof combines them.

## Proved and sorry left

The target declaration `etaleHomComparison_reversedExact` is reduced to the two
strictly smaller declarations below. Two sorries were added:

- `etaleHomComparison_reversedExact_shiftData` in
  `lean/Sheaf/SixFunctors/EtaleHomTransposeExactShiftData.lean`;
- `etaleHomComparison_reversedExact_commShift` in
  `lean/Sheaf/SixFunctors/EtaleHomTransposeExactCommShift.lean`.

## No longer needed

The target module no longer imports or directly cites the former ten proof-plan
nodes `def-pur-derived-internal-hom`, `def-pur-hom-complex`,
`lem-coef-etale-tensor-model-comparison`, `lem-pc-kflat-resolution`,
`lem-pur-rhom-global-sections`, `lem-sbc-derived-scalar-extension-counit-shift`,
`lem-sc-derived-hom-tensor-total`, `lem-weil-pbc-ringed-internal-hom-exact-restriction`,
`lem-weil-pbc-site-derived-tensor-descent`, and
`prop-pur-kinjective-resolutions-exist`. The split statements retain only the
published comparison-model interface from `lem-coef-etale-hom-thick-locus`.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan expands a full K-injective/K-flat sign computation,
which is not available as a completed declaration in the current library. The
route was therefore decomposed into the normalized shift-data statement and the
transpose shift-compatibility statement, each strictly below the target.

## New nodes

- `lem-coef-etale-hom-transpose-exact-shift-data`, for the shift and triangulated
  structures.
- `lem-coef-etale-hom-transpose-exact-comm-shift`, for the transpose's
  `NatTrans.CommShift` property.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.EtaleHomTransposeExact": "622f4a341d72fc100afe999c6c8b066086003b43", "Sheaf.SixFunctors.EtaleHomTransposeExactCommShift": "7dcb55aa38eec1b2c498a365967fcc6b059054b0", "Sheaf.SixFunctors.EtaleHomTransposeExactShiftData": "bc170c2e256bf3a1504e32a4b7320b7490d7005e"}, "results": {}, "time": "2026-10-28T07:13:25+0800", "transitive": 0, "version": 1}
```

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
