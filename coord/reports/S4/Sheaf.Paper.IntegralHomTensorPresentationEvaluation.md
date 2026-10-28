## What changed

Corrected and proved `WeilConjectures.IntegralHom.tensor_presentation_evaluation`.
The old arbitrary adjunction parameter becomes an existentially constructed
adjunction family, normalized using `ringedTensor_koszul_exists`. The proof
uncurries the supplied Hom-complex map using the existing chain equivalence,
precomposes with the signed exchange, and uses
`coefficientTensorCurry_normalize` to prove the localized counit square.
All data and formulas in TensorPresentation remain unchanged.

Added the fully proved `Sheaf.Paper.IntegralHomEvaluationCoefficient`, containing
`evaluate_eq_coefficient`. Kernel profiling isolated a 24-second definitional
check between the two existing evaluation notations. Its separate module keeps
that check and the main proof independently within the file-time gate. Explicit
choices and their specifications avoid expensive existential destructuring. This
adds no unfinished statement and changes no shared definition.

Adapted the unclaimed `Sheaf.Paper.IntegralHomTensorPresentation` constructor to
obtain the adjunction and its evaluation together. Its statement is identical.
Updated both DAG proof routes and the evaluation node's corrected statement,
Lean attachment and complete statement-change record. Change record:
`coord/changes/integral-hom-tensor-evaluation-normalization.md`.

Searches: LeanFinder for transporting right tensor adjunction through braiding
returned generic closed and rigid-category APIs. Loogle found
`Adjunction.ofNatIsoLeft` and its inverse-transpose equation. Project `rg`
found the already proved Koszul exchange, the chain uncurrying construction and
the exact representative normalization theorem. No unfinished statement is split
off. The proof uses the already proved public
`homComplexTensor_pure_equivalence`, the public normalization and exchange
statements, and Mathlib adjunction transport. No private source-library
construction is imported. A proof-only `import all` of Mathlib's HasLimits
module exposes the chosen-colimit definition needed to identify the two existing
total-tensor notations. No imported statement or definition changes.

Validation: clean import-order sandbox compilation passed without warnings.
The standalone evaluation API compiled in 31 seconds, the final main theorem in
48.5 seconds, and the unchanged-signature constructor in 9 seconds. The profiler
and diagnostic options are removed. All three files have zero sorry.

## Proved and sorry left

Original item: one sorry, in `tensor_presentation_evaluation`, node
`new-sf-integral-hom-models-exist-tensor-evaluation`.

The old universally quantified statement is false, so its hole is removed by a
recorded statement correction, not counted as a proof of the unchanged old
statement. The corrected `tensor_presentation_evaluation` is proved completely;
zero sorry remain in it. The new `evaluate_eq_coefficient` is also completely
proved by reflexivity and contains zero sorry. `tensor_presentation_exists`
remains completely proved with its original signature. No holes are added and none are split off.

Private helpers `swappedAdjunction`, `swappedAdjunction_uncurry`, `curry_counit`
and `map_comp_exchange` are real constructions/proofs and contain no sorry.
No axiom or hollow definition is added.

## No longer needed

Removed the item's unused proof import
`Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`.

Removed the constructor's proof import
`Sheaf.Paper.IntegralHomTensorPresentationAdjunction` and its DAG dependency
`new-sf-integral-hom-models-exist-tensor-adjunction`. The evaluation node also
no longer needs this dependency. The constructor was the only Lean importer;
the two nodes above were its only DAG parents. Both dependency routes are
updated here, so this module/node is no longer needed on this tensor-presentation
route. It is held by J4 and is neither deleted nor modified in this packet.

The generic closed-structure theorem remains needed by the constructor.
No unit statement or unit proof step is bypassed: this is the same tensor-Hom
evaluation argument, now using existing normalized component APIs.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old statement, corrected here): arbitrary adjunctions on
fixed functors are not equal as data. Twisting the right adjoint by minus identity
negates its counit. The signed chain formula is unchanged and uniquely determines
the chain map on pure tensor generators. Rank-one complexes in degree zero over
nonzero characteristic-zero integral coefficients (l=3 suffices) therefore
contradict the old demand for every adjunction to have that same counit.

The source uses the actual evaluation maps, so the correct result constructs the
adjunction together with its evaluation field. This retains all inputs, signs,
representative comparisons and the single adjunction working for every complex.
The unique citer `lem-sf-integral-hom-models-exist-tensor` still holds: its proof
now extracts the two fields together and builds exactly the original
TensorPresentation. No target statement or definition is changed.

The previous one-step plan cited an adjunction-existence lemma which provided
no evaluation normalization. The normalized Koszul exchange and uncurrying APIs
already supply the missing argument; none of those declarations is restated.

## New nodes

`new-sf-integral-hom-evaluation-coefficient` records the completely proved
`WeilConjectures.IntegralHom.evaluate_eq_coefficient` in
`Sheaf.Paper.IntegralHomEvaluationCoefficient`. It identifies the paper and
coefficient section-evaluation definitions at the same chosen product projection.
Its source is the evaluation step of the integral-Hom reduction, with Stacks
0A8X and 03EO. It is an elementary definitional API lemma, isolated for compile
time, and adds no sorry. The change record is
`coord/changes/integral-hom-tensor-evaluation-normalization.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralHomEvaluationCoefficient": "1b81766fd3856c6e56ab8fe4b864c8eaa7ec8f08", "Sheaf.Paper.IntegralHomTensorPresentation": "1ba8cb97a79538ad2caaf59469693865eb089e83", "Sheaf.Paper.IntegralHomTensorPresentationEvaluation": "d017003d16d3ab94ba60bcbefb0bc2f341c842b2"}, "results": {"Sheaf.Paper.IntegralHomModelsExist": {"hash": "0b8abf2fceaad79febc3ab025a333a597e4ccdd3", "status": "OK"}}, "seconds": 8, "time": "2026-10-28T11:12:36+0800", "transitive": 0, "version": 1}
```

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
