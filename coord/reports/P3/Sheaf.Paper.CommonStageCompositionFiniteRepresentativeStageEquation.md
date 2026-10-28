## What changed

Filled `WeilConjectures.commonStageCompositionFiniteRepresentative_stageEquation` in
`Sheaf.Paper.CommonStageCompositionFiniteRepresentativeStageEquation`, preserving its
statement. Added private proved helpers for heterogeneous congruence and the categorical
cancellation calculation. Added proof-only imports of
`Sheaf.Paper.PullbackTensorRationalCompositionCoherence`,
`Sheaf.Paper.CommonStageRationalCompositionNaturality`, and
`Sheaf.Paper.CompletedPullbackTensorNaturality`.

The proof uses the finite stage of the literal tensor object of the two inputs. It
normalizes every endpoint and represents both routes there, cancels the intermediate
comparison maps, and uses rational composition coherence and the two naturality squares.
Equality of the quotient classes then transfers the supplied representative of the left
route to the right route. No scalar-extension faithfulness is assumed.

Updated the item's DAG proof and dependencies to record those actual steps. The existing
rational compositor naturality theorem is used as a categorical tool; this does not
replace any step of the conventions unit (whose realized statement and steps are empty).

Validation: `lcompile.py` compiled the full delivered module cleanly in 14.7 seconds.
All three added imports passed the import-direction cycle checks.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.commonStageCompositionFiniteRepresentative_stageEquation`
(node `lem-pur-pullback-tensor-common-stage-composition-finite-representative-stage-equation`).
Zero holes remain in the delivered module, and zero holes or new assumptions were added.
The proof uses the existing normalized operation and constraint specifications, including
existing dependencies that still have their own proof obligations.

## No longer needed

None. No existing import, declared proof dependency, node, or module is pruned. The proof
completes the planned finite-stage argument and adds its naturality dependencies explicitly.

## Where the brief, the DAG or earlier work was wrong

The former one-step proof plan omitted two naturality squares needed after inverse
cancellation: compositor naturality for the tensor endpoint comparison, and pullback/tensor
naturality for the two input pullback comparisons. Both statements already exist and are
now used explicitly. The chosen representative at L need not be enlarged: prove equality
of the two quotient classes at the input tensor stage K first, and then compose with
`hleft`. No statement or definition was changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CommonStageCompositionFiniteRepresentativeStageEquation": "7031e70881d4e3f54938f92d551e6aa9b5639f88"}, "results": {"Sheaf.Paper.PullbackTensorCommonStageCompositionFiniteRepresentative": {"hash": "3f0baed801312cc0af5d0874b2fce9b9c548c124", "status": "OK"}}, "seconds": 91, "time": "2026-10-28T12:06:01+0800", "transitive": 0, "version": 1}
```

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
