## What changed

Repaired `WeilConjectures.podReindexingTensorRoosNormalization_model_iff_canonical`
in `Sheaf.Paper.PodReindexingTensorRoosStrict`. The former conclusion was a false
conjunction: the hypotheses fixed the strict tower but never constrained the
independent `T.tensor` field. The replacement is an actual equivalence between
Model and the canonical equation on precisely the representatives quantified over
by Model. It needs the forward generator law; naturality in representatives is
unnecessary for the pointwise argument.

The item proves invertibility of the ordinary-to-completed maps on constructible
inputs from CompleteUnit and the intrinsic/legacy completeness comparison. A small
proved categorical cancellation lemma then turns the single-pair strict Roos square
into both directions of the representative equivalence. The proof uses no
faithfulness assertion for finite evaluation.

Adapted the sole importer/caller, `Sheaf.Paper.PodReindexingTensorRoosNormalization`,
without changing its signature: its global Canonical hypothesis supplies the
canonical equation on each representative. Its original public TowerNaturality
hypothesis is retained for callers. The corresponding parent DAG proof is updated.
The change record is
`coord/changes/S7-pod-tensor-roos-representative-equivalence.md`.

## Proved and sorry left

The item's original false statement is corrected, not counted as an unchanged
statement proved. Its former named hole is removed and the repaired equivalence
has a complete Lean proof relative to the strict representative square. The proved
private helpers are `ordinaryComparisonIsIso`, `comparison_cancel`, and
`tensor_comparison_cancel`, and `representative_equivalence`.
There are zero `sorry`s in the item and zero in its adapted parent.

One new named hole remains:
`WeilConjectures.podTensorRoosRepresentativeSquare` in
`Sheaf.Paper.PodTensorRoosRepresentativeSquare`, node
`lem-pod-tensor-roos-representative-square`.

This is a repair and decomposition, with no net hole reduction: one former hole
removed, one genuine strict-representative calculation added. It is not a proof of
the former false conjunction. Unlike that conjunction or its replacement
biconditional, the remaining lemma contains no independently chosen derived tensor
family, no Model/Canonical conclusion, and concerns only one fixed pair and one
strict tower arrow. The combination with arbitrary tensor data, completeness and
cancellation is performed in Lean in the item.

## No longer needed

No existing public import is removed. The new single-pair module imports only
PodCompletionTensorModels, since it does not use Model or Canonical. No existing
module is withdrawn. No module is claimed globally pruned. The three original planned proof dependencies
(`lem-pod-reindexing-hom-resolution-model`, `lem-pur-kflat-total-tensor-model`,
`lem-pur-integral-operations-well-defined`) are not imported directly by the item:
its proof only needs the strict square and the completeness comparison. Those
three nodes remain needed by the strict square's proof plan and are not pruned
from the DAG. The item no longer needs TowerNaturality; the parent's interface
retains it unchanged. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the old statement claimed Model AND global Canonical for every
T satisfying Generators and TowerNaturality. Both hypotheses mention only T.tower;
neither mentions T.tensor. Keep the former fixed and twist a tensor comparison by
minus the identity on a nonzero completed rank-one constant tensor object (for
example over the 3-adic coefficients). The two hypotheses are unchanged, while
the claimed Canonical equation changes sign. Thus the old statement cannot be
proved as written. The parent's unused Canonical hypothesis in its old proof
exposed the error: that proof took the first conjunct of the false theorem and
never used the supplied canonical equation substantively.

The new representative equivalence also avoids a second unsupported inference:
without naturality of T.tensor, equations on actual localized representatives do
not determine its values at arbitrary isomorphic derived presentations. The parent
needs only the direction from its global Canonical hypothesis to Model, and that
statement is preserved verbatim.

The generic completeness bridge `lem-sf-derived-complete-legacy-comparison` is used
as a tool for its exact equivalence of the two completeness predicates; it does not
replace the unit's proof route. Mathlib searches (LeanSearch, LeanFinder, Loogle,
and source grep) found generic factorization/cancellation tools and no prescribed
strict completed tensor comparison. The supplied blueprint-ancestor helper cannot
resolve this already-created chain (it reports a missing blueprint ancestor); the
new node records the actual blueprint proposition and its Steps 1 and 5 directly.

Validation: the repaired item compiled in 34.0 seconds and its adapted sole
importer compiled in 3.7 seconds, in import order. The new square module previously
compiled in 38.0 seconds. The delivery tool repeats the final packet and consumer
checks against the server's current sources.

The first representative-square check took 62 seconds. Profiling
then checked it in 30.9 seconds (elaboration 17.9 seconds, kernel checking 8.54
seconds). Subsequent code uses local irreducibility of large functors and isolates
categorical rewriting in a generic helper, with transparency respected and no
raised compile-time limit. Development profiling options are removed.

## New nodes

`lem-pod-tensor-roos-representative-square`: for a fixed pair of complete
constructible K-flat representatives and a single generator-normalized strict
tower isomorphism, identify its localized two-coordinate Roos realization with
the canonical completed pullback/tensor arrow after transporting the two
representatives and the completion maps. This is the strict calculation before
comparison with any arbitrary derived tensor family. Its docstring and DAG proof
spell out the quotient-generator, coherent-transition, Roos-coordinate and
unit/counit normalizations. Its plan also names the existing full integral
tensor/Roos realization, whose prescribed normalization identifies the completed
tensor representative with the coherent-system model; this is a generic model
comparison, not a replacement for any realized unit step. The zero and empty-scheme cases are included. It is
independent of the false global Canonical claim.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingTensorRoosNormalization": "020e37ee89760f267cddf8353a07fa67ca530dfe", "Sheaf.Paper.PodReindexingTensorRoosStrict": "b2c085990d018d0aa9d7e5c5c911117722ef4133", "Sheaf.Paper.PodTensorRoosRepresentativeSquare": "a9b69801f6201db3f8a55eed3cb590153e586a16"}, "results": {}, "time": "2026-10-28T10:56:10+0800", "transitive": 0, "version": 1}
```

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
