## What changed

Added the proved theorem
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_derived_square_comparison`
in the assigned module. It constructs the comparison, proves the complete representative
square (including both exact-functor factorization maps), and proves uniqueness. Its
hypotheses omit the adjunction normalization and coherence assumptions that this component
does not use. The ordinary representative naturality hypothesis is retained.

The proof first identifies the supplied chain comparison by its summands. It then composes
the existing native and ordinary models on pairs consisting of an arbitrary complex and a
native K-flat complex. Product localization and fully faithful restriction descend this
natural isomorphism. Cancellation proves the square; faithfulness proves uniqueness.
All private helpers are proved. The total-tensor wrapper has exactly the existing objects
and maps; its functor laws are proved from `map₂CochainComplex`.

The original `native_weil_tensor_ringed_derived_square_native_data` signature and its
existing hole are preserved. Its coherence claim is marked `STATEMENT-DISPUTED` with the
specific missing compatibility described below. The new result is partial progress on
that claim, not a proof of coherence and not another unproved restatement.

Removed the unused public import of `NativeWeilTensorRingedDerivedSquareOrdinary`.
Changed `NativeWeilTensorRingedModelNaturality` to a proof-only import. Added proof-only
imports of Mathlib product localization and the existing bifunctor-comparison API.
All irreducibility attributes used to avoid unfolding large definitions are local.
The assigned node now records the proved component and the unresolved coherence step.

Validation: the assigned file compiled in 57.3 seconds and its unchanged direct parent,
`Sheaf.Paper.NativeWeilTensorRingedDerivedSquare`, compiled against it in 23.8 seconds.
The unchanged parent copy was then removed from the sandbox. The new theorem has a scoped
400000-heartbeat allowance for specialization of large dependent functor types; the
60-second limit per file is unchanged. No profiler or trace option remains.

## Proved and sorry left

Proved, with no new hole:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_derived_square_comparison`
(node `lem-sf-native-weil-tensor-ringed-derived-square-comparison`). This is an existence
and uniqueness theorem for the full representative square.

Closed original holes: **0 of 1**. Added holes: **0**. Split-off unproved statements: **0**.

The one remaining hole is
`AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_derived_square_native_data`
(node `lem-sf-native-weil-tensor-ringed-derived-square-native-data`). Its signature is
verbatim unchanged. The outstanding assertion is coherence of the uniquely prescribed
comparison. No definition contains a hole. No other module is modified.

## No longer needed

The new comparison proof uses the native model, its naturality, forgetting of K-flatness,
and `A.localization`. It does not require the previous step's fresh K-flat resolution
(`lem-pc-kflat-resolution`), the ordinary-data existence theorem, ringed forgetting descent,
or the underived/derived adjunction normalization equations. These are pruned from the
representative-square step of the assigned node, not asserted unnecessary for the
unresolved coherence step or for other consumers.

The `NativeWeilTensorRingedDerivedSquareOrdinary` import is removed here; the direct parent
imports that module explicitly and still uses its theorem. Its module and node therefore
remain needed globally. The public naturality import becomes private because only the
proof uses it. No Lean module or DAG node is withdrawn; global modules pruned: none.

## Where the brief, the DAG or earlier work was wrong

`STATEMENT-DISPUTED`: the second proof step says that conjugating `d.coherence` gives
coherence for the particular comparison fixed by `ordinaryModel`. Conjugation supplies
coherence for the transported ringed ordinary structure. To reach the stated conclusion,
one still needs a coherent identification of that structure with the supplied ordinary
models and adjunction. `hmonoidal` fixes `S.monoidal`, but does not fix `S.adjunction`.
`NativeAdjunctionNormalization` normalizes relative to the supplied adjunction and Hom
representatives. `NativeOrdinaryTensorModels` additionally controls signed symmetry;
neither definition explicitly identifies the comparison's associator with the canonical
one. `NativeClosedHomModels.ordinaryModel` and `.ordinaryRepresentatives` also have no
compatibility field with each other.

The categorical inference in the old proof is invalid in general. For example, in graded
rational vector spaces with the usual tensor and signed symmetry, multiply a tensor
comparison on homogeneous degrees `(a,b)` by the symmetric nonzero scalar `c(a,b)`, where
`c(1,1)=2` and every other value is 1. One can twist the tensor-Hom adjunction by the mate
of this natural automorphism, so binary adjunction normalization still holds. Symmetry
and the unit equations hold. Associativity would require
`c(a,b+c)c(b,c)=c(a+b,c)c(a,b)`, which at `(1,1,2)` says `1=2`.
Thus binary adjunction uniqueness and signed symmetry alone do not justify the claimed
monoidal identification. This is a counterexample to that general proof principle,
**not** a formal counterexample to the concrete native theorem.

A repair should identify the ordinary models/adjunction with the canonical coherent
ones, or supply and prove the missing compatibility for the actual construction. I did
not strengthen a hypothesis or weaken a conclusion to hide this issue. In particular,
no new unproved theorem simply asserting coherence was added. The uniqueness theorem
shows that choosing a different tensor comparison cannot resolve the gap while retaining
the displayed square.

The representative-square plan was also longer than necessary: its already supplied
localization and natural models suffice directly. Flat-term replacements and an orbit
retract are needed in the existing forgetting-K-flat theorem, which is used, but not
again in the descent argument here. The unit route is preserved.

## New nodes

`lem-sf-native-weil-tensor-ringed-derived-square-comparison` records the fully proved
existence and uniqueness component in the assigned module. It is a strict component
without a new hole. Its three Mathlib search records identify product localization,
fully faithful restriction, and natural-transformation descent.

Change record: `coord/changes/native-weil-tensor-ringed-square-comparison.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNative": "4e3bef5dda6f58803195beb5077a470320dfbbfb"}, "results": {"Sheaf.Paper.NativeWeilTensorRingedDerivedSquare": {"hash": "5b025cfd7e4859282042e936f945814922d493b6", "status": "OK"}}, "seconds": 25, "time": "2026-10-28T04:40:23+0800", "transitive": 0, "version": 1}
```

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
