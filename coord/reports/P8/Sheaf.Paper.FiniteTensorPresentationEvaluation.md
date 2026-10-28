## What changed

Corrected and proved `WeilConjectures.IntegralHom.finite_tensor_presentation_evaluation`
in `Sheaf.Paper.FiniteTensorPresentationEvaluation`. It constructs a normalized
left tensor-Hom adjunction using a symmetry with the recorded Koszul formula.
The repaired construction is stated for arbitrary coefficient ring sheaves;
no finite-coefficient fact occurs in the argument. The finite-level caller
instantiates the original ring unchanged. This generalization avoids the large
concrete coefficient types that profiling found in repeated kernel checks.
The proof uses the existing chain equivalence, the fixed injective-resolution
augmentation, pure-tensor extensionality, and the symmetry comparison square.
Added proved private helpers and the fully proved unsigned uncurrying module, with
no new obligations. The ringed-derived closed
structure import is public because its symmetry-model predicate occurs in the
corrected signature; the proved unsigned uncurrying module is imported privately.
That module imports the existing chain tensor-Hom construction privately with
`import all`.

Adapted the sole caller, `Sheaf.Paper.IntegralHomReductionComponents`, preserving
its `reduction_target_exists` signature. Its proof obtains the adjunction and
normalization together and builds the same `TensorPresentation`. Updated both
DAG proof plans and recorded the corrected statement with its sole citer.

Validation: all files compiled in import order through `lcompile.py`: the unsigned
helper (previous clean runs 31.0 and 55.6 seconds), item (46.4 seconds), adapted
caller (39.1 seconds), and unchanged direct importer
`Sheaf.Paper.IntegralHomReductionPresentation` (3.7 seconds). The unchanged importer
copy was removed after this check. The caller's declaration signature was compared
with the original and is identical.

Change record: `coord/changes/P8-finite-tensor-evaluation-normalization.md`.

## Proved and sorry left

Original item: one hole, `WeilConjectures.IntegralHom.finite_tensor_presentation_evaluation`
(node `new-sf-integral-hom-reduction-target-evaluation`). The old statement was false;
this delivery repairs it and supplies a complete proof of the corrected statement.
The original arbitrary-adjunction statement is not claimed as proved.

Source holes removed by the statement repair and complete proof: 1. Holes added: 0.
Holes left in delivered modules: 0. This is a repair of the false old proposition,
not a claim that the old arbitrary-adjunction proposition was proved.
All private helper proofs are complete. The caller's proof remains complete.
The new public theorem `WeilConjectures.IntegralHom.representative_uncurry_evaluation`
(node `lem-sf-integral-hom-representative-uncurry`) is fully proved. It is extracted
for compile performance, not left as a new obligation; split-off sorries: 0.

## No longer needed

No modules or DAG dependencies were withdrawn. The direct proof import of
`Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction` is confined to the new
unsigned uncurrying module. The generic closed symmetric
monoidal dependency remains necessary for the symmetry model. Its existing
chain-adjunction construction supplies the chain-equivalence calculations.
The caller no longer duplicates the transport of the adjunction across symmetry;
that construction is now inside the evaluation theorem so the two cannot diverge.
No proof-only dependency was added merely because it appears in an old plan.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old formulation): the previously arbitrary `adj` had no
normalization relating it to `S.adjunction` or `T`. Negating unit and counit gives
another adjunction, while the prescribed generator formula fixes the evaluation
map. For odd coefficient characteristic and the unit pairing these cannot both
hold. The corrected existential constructs exactly the transported adjunction
needed by `lem-sf-integral-hom-reduction-target`; the existing coherence witness
provides its symmetry normalization. That citer's statement still holds unchanged.
This is a statement repair with a real proof, not a proof of the false old statement.
The unit route and all target statements remain unchanged. The repaired statement
also uses the original coefficient tensor/generator and Hom-product projection
interfaces directly; their agreement with the integral presentation wrappers is
checked by compiling the adapted caller into the unchanged `TensorPresentation`
conclusion. Private helpers keep the adjunction construction from unfolding during
the representative verification.

## New nodes

`lem-sf-integral-hom-representative-uncurry`, in
`Sheaf.Paper.IntegralHomRepresentativeUncurry`, proves unsigned chain evaluation
and its right-tensor derived comparison. It applies to an arbitrary ring sheaf
on Y, needs no symmetry or finite coefficient hypothesis, and does not construct
the left-tensor adjunction or its signed evaluation. Its proof is complete.
After replacing expensive concrete rewrites by generic category lemmas, the
combined item still compiled in 96 seconds; this self-contained part was moved
to its own module to meet the unchanged per-file 60-second limit.

Change record: `coord/changes/P8-finite-tensor-evaluation-normalization.md`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteTensorPresentationEvaluation": "52fdf1e7f7343611401e005615fafc4303663c54", "Sheaf.Paper.IntegralHomReductionComponents": "3dbc7d3c53be1bf3305170407a7e04a7c8c0fd9d", "Sheaf.Paper.IntegralHomRepresentativeUncurry": "d95f0028a0e7261162017e11bd93a1f67fe8c859"}, "results": {}, "time": "2026-10-28T12:55:11+0800", "transitive": 0, "version": 1}
```

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
