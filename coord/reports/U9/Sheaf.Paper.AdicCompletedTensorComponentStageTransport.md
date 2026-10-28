## What changed

Replaced the proof hole in
`WeilConjectures.AdicQbarRealization.completedTensorCommonComponent_stage_transport`
with an explicit common-stage transport argument. The existing signature and docstring
are preserved. The new proof imports fixed-stage naturality and the finite scalar square.

The proof identifies the natural inclusion tensorator with `stageTensor` by its unique
normalization. It proves the composition formula for the actual `isoToStage` maps from
the stage-system cocycle. At the coefficient compositum it applies the two-field scalar
square, then fixed-stage naturality to the two scalar associators, and combines these
squares by functoriality and inverse cancellation. The final equation has precisely the
original endpoint isomorphisms, including the identity-extension case.

Validation: the finite scalar-square module compiled via lcompile.py, and the full
parent proof compiled in 34.9 seconds. Profiling options were removed afterward.
The original theorem signature was compared verbatim, all Lean lines are at most
100 characters, and both node dependency lists equal the union of their proof uses.

The representative calculation is stated in the new module
`Sheaf.Paper.AdicCompletedTensorFiniteScalarSquare`. It compares two specified finite
models and two rational objects at one source field. It does not mention
`completedTensorCommonComponent`, independently staged inputs, their compositum, or a
family of models at all coefficient fields. The parent performs the compositum,
associator, and conjugation work in Lean; it does not simply apply a renamed version
of its own statement.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.AdicQbarRealization.completedTensorCommonComponent_stage_transport`
(node `lem-sf-adic-completed-tensor-component-stage-transport`). Its proof is complete
relative to the imported named statements.

Added one hole:
`WeilConjectures.AdicQbarRealization.completedTensorStageComponent_scalar`, in
`Sheaf.Paper.AdicCompletedTensorFiniteScalarSquare`
(node `lem-sf-adic-completed-tensor-finite-scalar-square`). Its proof is exactly
`:= by sorry`; its docstring records the two-field K-flat, balanced-section and whole
completion-map argument. It requires only the two finite models, rather than a
common-stage component family.

This is a decomposition: 1 original hole closed, 1 lower hole added, net 0 holes.
The assigned module has zero remaining holes. The private inclusion normalization,
stage cocycle, and conjugation lemmas are proved, with no additional holes.

## No longer needed

No original public import was removed. The proof adds only private imports of the
finite scalar square and the existing fixed-stage naturality theorem. No module is
withdrawn or globally pruned.

The parent's former direct dependencies on finite-model representative normalization,
native `common_field`, and scalar-extension formulas are now used by the finite scalar
square. They remain needed there; this is not a claim that their modules can be pruned.
The updated parent proof dependencies record its actual normalization, finite square,
fixed-stage naturality, and stage-system cocycle argument.

## Where the brief, the DAG or earlier work was wrong

No statement correction is made. The former one-step proof plan combined the two-field
normalization calculation with common-stage endpoint bookkeeping. These are separated
without weakening either claim. The finite scalar square retains both models, actual
`isoToStage` maps, and the normalized reflexive scalar unit; no nonzero, nonempty,
faithfulness, strict-extension, or extra geometric hypothesis is added.

## New nodes

`lem-sf-adic-completed-tensor-finite-scalar-square` is the two-field normalization
step from the original plan, sourced to BS Definition 3.4.10, Proposition 6.8.14 and
Remark 6.8.15, and HRS Proposition 5.2 and Lemma 7.9. The node has an exact Lean
attachment, proof in words, three recorded searches, and the parent's chapter and
unit. The source places were checked in the local PDFs. Its edge cases include
E = F with possibly different normalized models, zero objects, and an empty scheme.
Blueprint searches for completed tensor scalar, normalized finite, scalar, and
completion found no exact finite-model square; the ancestor command confirms that
the parent has no imported blueprint ancestor. There are no changes to existing
modules besides the assigned item, no changed
public interface, and no change record is required.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicCompletedTensorComponentStageTransport": "2c645b89ef8cac4fa19ded40c1fc4781c485391a", "Sheaf.Paper.AdicCompletedTensorFiniteScalarSquare": "40bab11cd6924907f2e7f2f2a9b1d5eabe1538c9"}, "results": {"Sheaf.Paper.AdicCompletedTensorCommonComponentNaturality": {"hash": "c70a8ac3419adcbb0ed799b6b4119d67044d7820", "status": "OK"}}, "seconds": 19, "time": "2026-10-28T12:39:36+0800", "transitive": 0, "version": 1}
```

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
