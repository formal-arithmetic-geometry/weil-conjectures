## What changed

Reduced `WeilConjectures.pullbackTensorSystemComparison_evaluation` to the finite-evaluation
calculation on K-flat coherent representatives. Its proof now forms the two routes as natural
transformations, supplies a K-flat representative isomorphism for each input, applies the
representative theorem, and uses naturality and cancellation to obtain equality on arbitrary
coherent derived objects. The existing private resolution helper was moved earlier within the
same module so this proof can reuse it. The fully proved descent argument is a private helper in
the new representative module, to keep compilation of the large parent within the per-file
limit.

Added the proof import `Sheaf.Paper.CompletedPullbackTensorEvaluationRepresentatives` and its
one representative theorem. The helper imports the lower finite construction directly, avoiding
the eleven additional modules of finite coherence. The finite comparison is its actual
construction, definitionally equal to the parent's `canonicalFinitePullbackTensor`. It accepts
the ordinary unit normalization and the exact cochain descent normalization explicitly, avoiding
an import cycle with the parent. The parent supplies both from its existing unique-
characterization theorems. A proved private component equation and local irreducibility keep the
comparison constructions sealed during the descent proof; these are elaboration changes within
this delivery. The representative statement contains no assertion for arbitrary derived objects.
The public signatures, definitions and existing public imports are unchanged. Three previously
proved arguments now call proved private implementations in
`Sheaf.Paper.CompletedPullbackTensorProofImplementations`: exact-composite localization,
ordinary quotient/pullback units, and preservation of K-flatness. Their original proof terms
were moved without mathematical change; the original declarations keep their signatures. The implementation module exposes its fully proved exact-composite comparison for its DAG attachment; the other implementations are private. It introduces no hole.

Validation: all three Lean modules compiled successfully through remote `lcompile.py`. The
delivery command runs the required preflight and declaration/axiom probe. A first delivery
attempt stopped at the 60-second file limit; the proved descent argument was moved out of the
large parent and its rewriting reduced. Three existing proved arguments were also extracted into
a private implementation module after profiling showed that the remaining parent was still above
the time limit. No timeout limit, shared definition, public interface, or mathematical statement
changed.

## Proved and sorry left

This is a decomposition, not a net reduction of the hole count. One of the four original holes
is closed from one new, strictly narrower representative theorem; net holes closed: 0.

Closed in the item:

- `WeilConjectures.pullbackTensorSystemComparison_evaluation`, node
  `def-pur-completed-pullback-tensor-comparison`: the extension from K-flat representatives
  to arbitrary coherent derived inputs is proved by naturality and resolution isomorphisms.

Three original holes remain untouched, all on node `def-pur-completed-pullback-tensor-
comparison`:

- `WeilConjectures.canonicalFinitePullbackTensor_quotient`.
- `WeilConjectures.canonicalCommonStagePullbackTensor_existsUnique`.
- `WeilConjectures.canonicalIntegralPullbackTensor_scalar`.

One hole is added:

- `WeilConjectures.completedPullbackTensor_evaluation_representatives`, node
  `lem-pur-completed-pullback-tensor-evaluation-representatives`.

The representative theorem is strictly the K-flat calculation of the original docstring: it does
not assert the result for arbitrary derived inputs. Its normalization hypotheses fix the already
existing ordinary and derived comparison isomorphisms; they do not assume the desired tensor
square. The main proof performs the separate descent step.

Edge cases checked in the statements and natural-language proof: zero complexes, empty schemes,
the first quotient n=0, identity morphisms, unbounded cochain diagonals, and K-flat complexes
whose terms need not be flat. No additional boundedness, constructibility or termwise-flatness
assumptions are introduced in the original theorem.

## No longer needed

No nodes or modules are pruned: all existing mathematical routes and the unit route remain
needed. Five direct proof imports leave the parent because the moved K-flat implementation
now imports them itself: `Sheaf.Paper.KFlatRingedToposPullback`,
`Sheaf.AlgebraicGeometry.ProEtaleEnoughPoints`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange`,
`Sheaf.Algebra.Homology.AlgebraicInverseImageKFlat`, and
`Sheaf.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients`. These modules remain
in the delivery's import closure. The parent imports
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` directly for its resolving
representative theorem. The new representative import is necessary for the K-flat square.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing docstring's K-flat calculation and extension
by naturality were not separately stated in the DAG. This delivery records that separation and
completes the extension step. The remaining representative calculation has its source, proof in
words and exact Lean signature in its own module and node.

## New nodes

`lem-pur-completed-pullback-tensor-evaluation-representatives`, in `dag/nodes/sec-smooth-purity/`, states the normalized finite-evaluation square only on a pair of K-flat coherent
complexes. Source: Stacks 07A4, the ordinary total-complex comparison, with the fixed sequence
evaluation and inverse-image units (0941, 03D2). Its public theorem is in
`Sheaf.Paper.CompletedPullbackTensorEvaluationRepresentatives`. The original node's proof and
proof dependencies now record this reduction. Change record: `coord/changes/F1-completed-pullback-tensor-evaluation.md`. No existing public interface or definition changed.

`lem-pur-completed-pullback-exact-composite`, in `dag/nodes/sec-smooth-purity/`, records the
fully proved localization argument already used by the parent. Its canonical cochain
factorization square and uniqueness are unchanged. The declaration
`WeilConjectures.completedPullbackDerivedCompositeIso_existsUnique` in the implementation
module has no `sorry`. This node supplies the attachment required for that new module.
Change record: `coord/changes/F1-completed-pullback-tensor-evaluation.md`.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
