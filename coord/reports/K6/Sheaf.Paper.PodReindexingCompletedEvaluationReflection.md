## What changed

Implemented `WeilConjectures.PodCompletedReflection.reindexing_laws` as a complete
assembly from the tensor-augmentation square and ambient ordinary M-first
currying. Its five clauses now have explicit proofs: the normalized unit square;
the transported reflector bijection; completed evaluation compatibility;
completed transpose compatibility; and both internal-Hom variances.

Added `Sheaf.Paper.PodReindexingOrdinaryCurrying` and the proved helper module
`Sheaf.Paper.PodReindexingOrdinaryBraiding`. The latter reuses the proved
private representative symmetry helpers through a proof-only `import all`, applies
the specified signed braiding on simultaneous K-flat representatives, extends the
square by K-flat resolutions, and uses the existing ordinary transposition theorem.
An abstract category lemma transports currying across an equality of functors.
The ambient theorem takes the closed structures and tensor models as parameters;
the assigned module instantiates it with the original calculus records.

The new assembly uses checked auxiliary calculations and a proved abstract
isomorphism-transport lemma for precomposition bijectivity. A private abstract-category
lemma proves naturality of the transported Hom comparison. Ordinary currying keeps
the comparison as a composite isomorphism, so its application does not expand the
coefficient sheaf. The augmentation statement takes the actual unit together with its defining
equation, and keeps the comparison as a composite isomorphism. The calculus is locally irreducible only within
the new theorem's section; existing definitions and proofs are unchanged.

Added `Sheaf.Paper.PodReindexingTensorAugmentationSquare` for the remaining strict
quotient/Roos normalization step. This statement concerns the actual tensor unit
and the original ordinary/completed tensor comparisons, without any evaluation or
internal-Hom conclusion. Existing signatures and public imports are preserved.
The assigned module compiled in 20.2 seconds; the ordinary currying module compiled
in 6.1 seconds and the augmentation module in 4.6 seconds. The delivery tool runs
the final compile and preflight checks after removal of diagnostic options.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PodCompletedReflection.reindexing_laws`
(node `lem-pod-reindexing-completed-evaluation-reflection`) by decomposition.

Proved the new ambient theorem `WeilConjectures.podReindexing_ordinary_currying`
(node `lem-pod-reindexing-ordinary-currying`) and the separate signed-braiding square
`WeilConjectures.PodReindexingCoherence.podReindexingOrdinaryBraiding`
(node `lem-pod-reindexing-ordinary-braiding`), with their private representative
and abstract transport glue, from the existing stated ordinary dependencies.

One original hole remains:
`WeilConjectures.PodCompletedReflection.identity_composition`
(node `lem-pod-reindexing-completed-evaluation-reflection`).

One hole is added:
`WeilConjectures.podReindexing_tensor_augmentation_square`
(node `lem-pod-reindexing-tensor-augmentation-square`). Thus one of the two original
holes is closed, one is split off, and two holes remain in the delivery. This is a
decomposition, not a net reduction in the number of holes.

## No longer needed

No existing imports, declarations, modules or nodes are withdrawn. Both original
normalization dependencies remain necessary. The standalone ordinary helpers use
supplied closed structures and tensor models, so they do not import
`Sheaf.Paper.PodCompletionReindexModels` or depend on
`def-coef-derived-system-calculus-data`; the assigned module still needs that data.
The new currying proof uses the
existing ordinary evaluation and representative symmetry API rather than adding
another completion or constructibility hypothesis. The augmentation lemma only
needs the completion/tensor data interfaces, not the existential completion-family
theorem.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is changed. The original plan correctly invokes ordinary
M-first currying, but the public ordinary evaluation API presents Hom-first
currying. The new proved lemma supplies the signed change of order explicitly,
using the recorded representative comparison; it applies to arbitrary ambient
unbounded objects. The completion-unit tensor square remains the precise missing
normalization step. The identity/composition theorem remains unchanged.

The new statements were checked on the identity isomorphism, zero inputs, and the
empty scheme: the same generator/localization arguments apply, without a geometric
nonemptiness condition or a finite Tor bound. The equal-functor parameter is an
equality, so its transport is proof independent.

## New nodes

`lem-pod-reindexing-ordinary-currying` records ambient signed M-first currying under
the normalized reindexing comparison, with no completion or constructibility
hypotheses. It is strictly an ordinary step in the completed evaluation argument.
Its source is blueprint dual-Tate compatibility Steps 2 and 4, Stacks 07A4/08J9,
and the existing ordinary comparison representative proof. Its searches found
ordinary closed-category and sheaf pullback APIs, but no statement fixing these
particular representative normalizations.

`lem-pod-reindexing-tensor-augmentation-square` records only commutation of the
actual ordinary-to-completed tensor augmentation with the two normalized tensor
comparisons. The proof plan uses the strict quotient tensor generators, adjunction
unit law, and both Roos product coordinates. It is the normalization step of
blueprint dual-Tate compatibility Steps 2 and 4, Stacks 07A4/099M. Its searches found
ordinary adic-completion tensor naturality and generic condensed monoidal APIs,
which do not give this derived sheaf normalization.

`lem-pod-reindexing-ordinary-braiding` is the proved ambient signed tensor square
used by ordinary currying, separated to keep each compilation within the time limit.
Its source and searches are the same representative symmetry argument as currying.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingCompletedEvaluationReflection": "da55a69996fc689ebc7f955006772d79ffe1678b", "Sheaf.Paper.PodReindexingOrdinaryBraiding": "524cec829965da2fa00b034690b87bad72670a4a", "Sheaf.Paper.PodReindexingOrdinaryCurrying": "0ccd61c6043126b871dda4ddb514700f505428bb", "Sheaf.Paper.PodReindexingTensorAugmentationSquare": "01f63ca1accc0a7dcdeda0fbeb32b9cd4b36ad73"}, "results": {"Sheaf.Paper.PodReindexingHomCoefficientDescent": {"hash": "b31a20e446b4ccb516f5b4cdfc07357860cc081d", "status": "SLOW"}}, "seconds": 143, "time": "2026-10-27T23:20:44+0800", "transitive": 0, "version": 1}
```

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
