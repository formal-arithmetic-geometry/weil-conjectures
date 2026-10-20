## What changed

Proved `WeilConjectures.SemilinearSections.normalized_inverseImage_closure` in
`Sheaf.Paper.SystemNormalizedTensorClosure`. All existing signatures, definitions,
imports, and docstrings are preserved. This is a partial proof delivery.

Let G be the accessor for the inverse-image geometry supplied by A. Its pull-transition
formula is `(A.geometric J' uInv uPush adjSet).property.2.1`. For each h, normalization
of P supplies the IsIso instance of its actual reduction. Every factor on the right
of the pull-transition formula is then invertible: a functorial image of a pull
evaluation isomorphism, an inverse coefficient-pullback comparison, and the inverse
image of the original reduction. `IsIso.of_isIso_fac_right` cancels the target pull
evaluation isomorphism. The transition-formula conjunct is the same supplied formula;
the cocycle conjunct is G.target.reduction_cocycle on the actual pulled-back object.
This preserves the unbounded setting and introduces no flatness hypotheses.

Validation: the item compiled through lcompile.py without errors or warnings after
replacing the unnecessary haveI with have. LeanFinder, Loogle, and grep searches
through msearch.py found the generic IsIso cancellation lemma. Searches of both
library roots found no duplicate of the two item declarations.

## Proved and sorry left

Closed 1 of the original 2 holes:
`WeilConjectures.SemilinearSections.normalized_inverseImage_closure`.

One original hole remains unchanged:
`WeilConjectures.SemilinearSections.normalized_tensor_closure`
(blueprint: lem-pur-system-normalized-tensor-closure).

Added zero holes and split off zero statements. Net hole reduction: one.
The remaining tensor proof needs the actual horizontal tensor transition-adjoint
formula in its second conjunct. The representative normalization fields specify the
canonical comparisons, but the formula itself is not a field of Data or a currently
stated semilinear theorem. The inverse-image formula, by contrast, is already a
proposition supplied by the geometric model. No assertion that tensor closure
follows merely from joint detection of isomorphisms is made.

## No longer needed

None. The existing imports and DAG proof dependencies are retained for the unchanged
pending tensor theorem. No node or module is withdrawn. The completed inverse-image
proof only uses the semilinear-section geometry and ordinary categorical preservation
and cancellation of isomorphisms.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement change was found. The inverse-image portion of
the stated plan is supplied directly by the geometric model's PullTransitionFormula
and the target Data.reduction_cocycle. The tensor portion still needs its distinct
representative-level transition identification; the existence of a canonical scalar
tensor comparison alone is not that identification. This delivery does not change
that pending plan or claim to have completed it.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
