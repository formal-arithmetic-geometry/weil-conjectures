## What changed

Replaced the hole in `Sheaf.Paper.AdicFiniteIntegralTensorReindexing` by categorical
pasting of an ordinary scalar tensor square and an integral completion square.
The original theorem signature, hypotheses, public import and conclusion are unchanged.
The three new proof imports are private.

`AdicTensorPresentationComparison` constructs `tensorPresentationComparison` by
fully faithful restriction to pairs of good complexes, comparing the supplied
normalized tensor model with the fixed ambient tensor model. It defines the
transported completion map `tensorPresentationCompletion` and ordinary scalar
isomorphism `finiteAmbientScalarTensor`. The proved `finiteIntegralTensorMap_factor`
identifies the original finite tensor map with their composite. No data is chosen
from a mere existence assertion: the preimage is uniquely determined by full
faithfulness and is constructed with `FullyFaithful.preimageIso`.

The main proof applies the two new squares, naturality of `V.derived`, naturality
of the inverse scalar tensor isomorphism, and functoriality. Thus the last pasting
step of the original plan is implemented in Lean rather than restated as a hole.
Local irreducibility and explicit `congrArg` pasting keep large derived-functor
constructions out of rewrite matching; no transparency checks are disabled.
The main module compiled in 15.5 seconds before removal of profiling diagnostics;
the delivery tool checks the cleaned final files again.

## Proved and sorry left

Closed the original body of
`WeilConjectures.AdicQbarRealization.finite_integral_tensor_reindexing` (1 of 1
original holes). There are zero holes in that module and in
`AdicTensorPresentationComparison`; its factorization theorem is proved.

Added two holes, each in its own module:

- `ordinary_scalar_tensor_reindexing`, node
  `lem-sf-adic-ordinary-scalar-tensor-reindexing`: the ordinary scalar square on
  arbitrary ambient derived integral inputs. It has no completion map and uses no
  complete-input identification.
- `tensor_completion_reindexing`, node
  `lem-sf-adic-tensor-completion-reindexing`: the integral quotient-completion square.
  It has no native realization, scalar extension, finite normalization, or native
  scalar/tensor reindexing data.

This is a decomposition, not a completed proof of the underlying mathematical
obligation: one upper hole is closed and two strictly separate lower holes are
added. In particular neither new theorem is the original theorem renamed or with
its hypotheses repackaged. Both retain zero and uniformizer-torsion inputs. The
ordinary square needs no constructibility; the completion square uses the full
normalized product and shifted mapping-fiber coordinates, without a claim that
finite quotient evaluation detects arbitrary derived morphisms.

## No longer needed

The presentation-comparison module does not import the ambient reindexing construction;
that public import is confined to the two new square statements that use it.
No existing module or declaration is withdrawn, and no global dependency is claimed
pruned. The old parent proof dependencies are distributed to the two genuine
subarguments. The parent no longer directly performs chain-generator calculations
or coherent completion reconstruction. These remain required in the children.

Unused sandbox-only experiments with `IntegralOrdinaryTensorReindex`, its existence
construction, and `ordinary_scalar_tensor_square` were removed before delivery.
They were never repository declarations. Using the already available fixed ambient
`podCompletedAmbientTensor` avoids introducing another tensor reindexing structure
and an additional existence obligation.

## Where the brief, the DAG or earlier work was wrong

No false statement or assigned repair was found. The current queue row is a proof
assignment with one hole; there is no module build-error file or quarantine row.
The existing declarations are adequate to express the two portions of the plan.

The proof data use tensor presentations whose functors need not be definitionally
equal. The explicit fully faithful presentation comparison handles this transport;
identifying the presentations by definitional equality would lose their model
normalizations. All original targets and source-library interfaces are preserved.

## New nodes

`def-sf-adic-tensor-presentation-comparison` records the concrete comparison,
transported ordinary scalar tensor and completion maps, and proved factorization.
It introduces no hole.

`lem-sf-adic-ordinary-scalar-tensor-reindexing` records exactly the ordinary balanced
scalar/generator portion of the parent proof, with its representative descent.

`lem-sf-adic-tensor-completion-reindexing` records exactly the integral quotient/Roos
completion portion, including the actual canonical pullback/tensor comparison.

The original node's proof, proof dependencies and proof origin now follow the Lean
pasting. No existing statement or definition changes, so there is no change record
for a repaired interface.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicFiniteIntegralTensorReindexing": "a90c801e09b0e8787d739ed098560ec03733c9a3", "Sheaf.Paper.AdicOrdinaryScalarTensorReindexing": "d9043c60589b2e4315b5b7c19884d557094feab5", "Sheaf.Paper.AdicTensorCompletionReindexing": "c57e241969dfb49c1098283247baa1f21d0c32ed", "Sheaf.Paper.AdicTensorPresentationComparison": "70e44010f2d740984a984c28231b1d069fea88fa"}, "results": {"Sheaf.Paper.AdicReindexingTensorIntegralCancelled": {"hash": "31a5ef3e5481dff6bdf7f1d388ff2e4a30357fb3", "status": "OK"}}, "seconds": 131, "time": "2026-10-28T14:59:19+0800", "transitive": 0, "version": 1}
```

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
