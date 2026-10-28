## What changed

Filled the proof of
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_underived_iso`
in `Sheaf.Paper.NativeWeilTensorRingedUnderivedIso`, preserving its statement.
The normalized uncurrying equation expresses each inverse component as a
representing tensor-Hom mate. Naturality of the native parameter adjunction,
the native Hom comparison, the ringed tensor-Hom equivalence, and the braiding
proves naturality for an arbitrary pair of morphisms. Proved private
helpers isolate normalization, the native Hom square, and the parameter adjunct
calculation; the inverse naturality theorem and a generic composition lemma
keep elaboration bounded.
The inverse components
then assemble into a natural isomorphism. Updated the item's DAG proof to
record this calculation. No definition, statement, or import changed. A scoped unused-section-variable
linter setting preserves the original complex-total instance binder.

Validation: the complete module compiles cleanly through `lcompile.py` in
40.7 seconds, within the 60-second per-file limit. The public theorem signature
and imports are byte-identical to the original; temporary probes were removed.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_underived_iso`
(node `lem-sf-native-weil-tensor-ringed-underived-iso`).

Zero holes remain in the item. Zero holes added; zero split-off statements.
The new private lemmas `compose_naturality`, `normalized_uncurry`,
`native_hom_naturality`, `parameter_adjunct_map`, and `inverse_naturality` are
all proved, with no postponed proofs.

## No longer needed

None. The proof uses the existing underived-data dependency and its fields.
No imports, modules, or DAG dependencies are removed. The unit route is kept.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The single naturality step can be
proved directly from the existing data and Mathlib APIs, without another
split. Searches with Lean Finder, Loogle, and grep located the parameter
adjunction naturality lemmas; the actual ringed naturality lemmas are already
proved in the adopted source library's `MonoidalClosed` module.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeWeilTensorRingedUnderivedIso": "98534d8c2bbc32c98533d4c6f68fbd48de44d9ee"}, "results": {"Sheaf.Paper.NativeWeilTensorRingedChainData": {"hash": "9dcd7d9ef41defd00709ff0b5246679e609fb2ef", "status": "OK"}}, "seconds": 97, "time": "2026-10-28T08:22:58+0800", "transitive": 0, "version": 1}
```

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
