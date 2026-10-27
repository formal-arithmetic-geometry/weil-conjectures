## What changed

Replaced the hole in `Sheaf.Paper.IntegralProjectionSystemEvaluation` by a proof
using the finite coefficient realization theorem in the new module
`Sheaf.Paper.FiniteIntrinsicProjectionRealization`.

The private `SystemEvaluationProof.system_projection_evaluation` reuses the
proved proper-evaluation, open-evaluation, compositor, equality-cast and word
pasting calculations of `Sheaf.Paper.SystemProjectionFormulaCoherence`, imported
with `import all`. Its public evaluation wrapper requires separated structure
maps and domain membership, but none of these assumptions is used by its
calculation. The local proof retains that calculation with explicit structure
maps and arbitrary system inputs. No other existing module or signature is changed. The item removes its local
irreducibility annotation on pullbackTensorCalculus so that the calculus finite
tensor is definitionally recognized in the intrinsic evaluation calculation;
this local annotation has no downstream effect.

Three proved private categorical helpers express tensor-input naturality,
projection-square pasting and the final endpoint reassociation abstractly. They avoid searching through concrete
projection terms during rewriting. Local irreducibility annotations protect
projection and realization definitions; instance removal is scoped to each
declaration and changes no exported attribute.

The final proof constructs b by composing evaluationTensor with the finite
comparison, applies the unrestricted evaluation calculation to the actual
reduction systems, and pastes the finite realization equation using naturality
of the comparison in both variables. It retains the exact specified endpoint
isomorphisms, including the datum's finiteSupport and finitePullback.

## Proved and sorry left

Closed the original textual hole in
`WeilConjectures.IntegralProjectionReduction.integralProjectionSystemEvaluation`
(node `lem-sf-integral-projection-system-evaluation`). The new private system
evaluation lemma and all three categorical helpers have complete proofs.
The full item compiled successfully with the new dependency (18.3 s); profiling
options used during debugging have been removed for delivery. The finite-only
module also compiled successfully. The delivery tool repeats compilation and
preflight against its own current checkout.

Added one hole:
`WeilConjectures.IntegralProjectionReduction.finiteIntrinsicProjectionRealization`
(node `lem-sf-finite-intrinsic-projection-realization`). This is a decomposition,
not a net reduction of the hole count: one upper hole closed, one finite-only
hole added. The item now has zero holes; the new module has one.

The remaining theorem compares intrinsic and fixed presentations at one positive
finite quotient. It contains no coefficient systems, o or z, integral inputs,
reduction systems, system projection, evaluation, or reconstruction assertion.
The combining proof, including the system projection evaluation and the
endpoint pasting, is complete. The finite theorem includes arbitrary finite
inputs and arbitrary input isomorphisms, so future work can prove it without
revisiting system evaluation or integral reductions.

## No longer needed

The direct proof-dependency citation `lem-sf-projection-scalar-square`
(`Sheaf.Paper.ProjectionScalarSquare`) is replaced by the proved system
proper/open evaluation calculations. No import of that module is added.
This is local pruning of the item's proof dependency, not withdrawal of the
module: other consumers may still need it. All original public imports remain.
No modules or declarations are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The existing public `SystemProjectionFormula.projection_evaluation` has unused
separated-structure-map and finite-domain hypotheses. SixFunctorSpace imposes
neither separatedness of structure maps nor those system-domain hypotheses.
The private calculations give the stronger identity actually needed here;
they have been reused locally without changing their source module.

The original plan did not supply a declared theorem for the finite
intrinsic-to-fixed tensor/projection realization step. The new finite-only
statement isolates that step. It is strictly a part of the argument rather
than the system evaluation statement renamed: all system, evaluation and
integral content is discharged in the original module.

The generic proved system evaluation calculation is used as a tool from
`lem-pur-system-level-projection-formula-coherence`, of unit
`sk-thm-sf-compatibility`. Only its already proved evaluation calculations are
used; its unfinished global coherence conclusion is not assumed. The item's own
unit `sk-rem-sf-pf-done` is a remark with no realized steps; its projection route
is retained. The foreign unit is used as a calculation tool because the item's
own declared scalar-square result concerns scalar extension rather than
evaluation of a strict system. No maintainer tool_uses approval is edited. The new finite-only
statement was checked on m=0 (exponent one), zero inputs, identity opens and
empty schemes: every comparison is the same universal tensor/adjunction map,
and there is no nonzero or nonempty assumption.

## New nodes

`lem-sf-finite-intrinsic-projection-realization`, in
`dag/nodes/sec-six-functors/lem-sf-finite-intrinsic-projection-realization.json`,
states the remaining finite comparison. Its module contains exactly one named
public theorem with its full source and proof in words. Library and blueprint
searches found no theorem with this finite comparison and these prescribed
endpoints. Mathlib searches (LeanSearch, LeanFinder, Loogle and grep) are logged
in searches.jsonl and recorded on the node. No change record is needed because
no existing statement, definition, exported attribute or public import changes.

The proved finiteProjection_operationPresentation was also inspected. It gives
only Nonempty of an arrow isomorphism, and its docstring explicitly disclaims
equality of prescribed endpoint comparisons. It therefore cannot discharge the
finite-only statement here. finiteScalarTensorPullbackComparison gives a pair
of tensor comparisons separately for each morphism; it does not provide the
single family on all spaces required here.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
