## What changed

Replaced the hole in `WeilConjectures.IntegralSystemRealization.integralRingedModelExistence`
by an assembly proof, with its signature and docstring unchanged. The proof fixes the ordinary
tensor to `calculus.integralClosed.tensor` and restricts that calculus's own representative
comparison. Thus both `tensorClosed` and the newer `tensorRepresentative` field are proved
by construction. The quotient chain is the existing constructed `quotientChain`, and its
normalization follows from `tensorOperationUnit_normalized`.

The actual open unit is proved invertible from the derived slice presentation. The open
projection is assembled from the existing `openProjectionIso` and its proved naturality;
its prescribed transpose follows by cancellation of the adjunction equivalence. The
reverse open base-change map and clopen map are explicitly constructed, with naturality
proved, from precisely the required unit transposes. The remaining assertions concern
invertibility of those particular maps, not existence of unrelated isomorphisms.

Five new modules separate the fixed tensor construction, tensor completion on one
scheme, pull completion for one morphism, cartesian invertibility of the specified
open mate, and clopen invertibility of the specified inverse-unit transpose. The tensor and pullback comparisons are proved
from the existing coefficient-model descent and strict tower comparisons. The fixed tensor
and private descent constructions occupy a separate module so that
normalization is checked against an abstract comparison structure. The existing
item node and five new nodes record this route. All added imports of the item are private
proof imports. No existing module other than the assigned item is changed, and no existing
public import, statement or definition is changed.

Validation: all six delivery modules compiled through `lcompile.py`. The final
profiling-free tensor module and assigned existence module were compiled together
after the assembly check. Every new node records its literal Lean signature; the
assigned statement and docstring remain verbatim. No temporary check module is delivered.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.IntegralSystemRealization.integralRingedModelExistence`
(node `lem-sf-integral-ringed-model-existence`). There are zero holes left in the item module.

The new tensor and pull-completion theorems are proved without new holes:
`WeilConjectures.IntegralSystemRealization.integralRingedTensorCompletion` and
`WeilConjectures.IntegralSystemRealization.integralRingedPullCompletion`.

Added two named theorem holes, each with its source and complete proof in words:

- `WeilConjectures.IntegralSystemRealization.integralRingedOpenMate_isIso`
  (`lem-sf-integral-ringed-open-base-change`).
- `WeilConjectures.IntegralSystemRealization.integralRingedClopenMap_isIso`
  (`lem-sf-integral-ringed-clopen-comparison`).

This is a decomposition: one upper hole closed and two smaller holes added, not a
sorry-free proof of the existence theorem. The ordinary tensor, reverse mate and clopen
map are real definitions without holes. The open-unit proof and both naturality proofs
are complete. No axiom or hollow definition is introduced. The residual assertions cover
empty schemes, identity opens and zero complexes; they impose no nonempty or geometric
finiteness assumptions.

## No longer needed

No original Lean import was removed. No module is withdrawn, and no whole module is claimed
pruned from the targets' closure. The original direct proof dependencies
`def-pur-completed-pullback-tensor-comparison`,
`def-sf-pull-completion-comparison`, `def-sf-tensor-completion-comparison`,
`def-sp-proetale-ordinary-tensor-pullback-total`,
`lem-coef-derived-system-evaluation-calculus` and `lem-coef-semilinear-derived-sections`
are no longer direct steps of the item's assembly proof. The coefficient calculus and
completion-comparison definitions remain needed by the tensor and pullback subarguments;
the relevant dependencies are retained in their new nodes. The finite/rational
completed-pullback tensor comparison and semilinear derived-global-sections theorem are
not used to assemble these ordinary completed-ring open comparisons. No proper/open
interchange theorem or system realization is imported as a replacement for this item.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies give definitions and broad coefficient calculations rather than
an already assembled instance of every required normalized comparison. In particular,
`tensorCompletionModel_nonempty` has quasi-compactness, quasi-separatedness and residue-field
invertibility assumptions, which are absent from this all-schemes item. It cannot be
applied here by adding those assumptions. Furthermore it does not assert the fixed
calculus representative equation now required by `RingedModels.tensorRepresentative`.
The ordinary tensor is therefore fixed directly to the calculus representative before
isolating its completion comparison.

The existing ordinary open-projection theorem already proves the projection and its
invertibility for arbitrary coefficient tensor models, so no additional projection hole
is needed. Private proof imports expose its naturality lemma and the derived slice
presentation without changing any public interface. The unit route of
`sk-thm-sf-compatibility` is retained; none of its realized statements or steps is bypassed.

## New nodes

`def-sf-integral-ringed-tensor-descent-data`:
`Sheaf.SixFunctors.IntegralRingedTensorDescentData` defines the fixed ordinary calculus
tensor and restricts its representative isomorphism. The same module contains the
proved private localization and strict-tower descent helpers used by the tensor theorem.
There are no holes in this module.

`lem-sf-integral-ringed-tensor-completion`:
`Sheaf.SixFunctors.IntegralRingedTensorCompletion` proves the quotient-completion comparison
for the fixed ordinary tensor and its representative augmentation
equation on one scheme using the existing descent theorem. This omits pullback and all opens.

`lem-sf-integral-ringed-pull-completion`:
`Sheaf.SixFunctors.IntegralRingedPullCompletion` proves the normalized `Pull` presentation
at one morphism, transporting the geometric coefficient pullback to the ambient model
and descending its strict quotient-tower comparison. It asserts neither tensors nor open
comparisons.

`lem-sf-integral-ringed-open-base-change`:
`Sheaf.SixFunctors.IntegralRingedOpenBaseChange` constructs the reverse mate and proves
naturality. Its sole unfinished theorem says this particular map is invertible for a
cartesian open square; tensor and completion models are absent.

`lem-sf-integral-ringed-clopen-comparison`:
`Sheaf.SixFunctors.IntegralRingedClopenComparison` proves invertibility of the actual open
unit and constructs its geometric transpose. Its unfinished theorem says that transpose
is invertible when the immersion is also closed. It has no tensor, pull-completion or
base-change inputs.

No change record is needed: no existing signature or shared definition was changed.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
