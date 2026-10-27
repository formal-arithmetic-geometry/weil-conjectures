## What changed

The original module (2230 lines; the published version uses 61-74 s of CPU when
compiled alone, over the 60-second limit for one file) is split verbatim into four
modules, each publicly importing the previous one:
`Sheaf.Paper.DerivedAutomorphismHomEvaluationBase` (the partial closed interfaces and
the finite comparison), `…ContinuationA` (integral, rational and common closed
data and transport, systems, completed reindexing), `…ContinuationB` (reduction
normalization, signed shifts, coherence, argument-first and shift squares), and
the item module (the target theorem). Every declaration keeps its signature and
body. The item module publicly imports `…ContinuationB`, so its importers see the
same declarations as before. The finite comparison laws theorem is decomposed
into two named components. `podFiniteHomComparison_naturality` is the naturality
clause, and `podFiniteHomComparison_laws_remaining` is invertibility, evaluation and
transposition. `podFiniteHomComparison_laws` is proved from the two.

Two helpers that were `private` in the original are now public, each with its
node, because the split puts them in a module of their own:
`podPartialClosed_ext` (ContinuationA, used by `podIntegralClosed_existsUnique`)
and `baseChangeHom_evaluation` (moved next to its only user in ContinuationB,
`podSystemHomComparison_realizedEvaluation`).

## Proved and sorry left

Proved: `podFiniteHomComparison_laws`, from its two components (a decomposition,
not a proof), and the helpers `podPartialClosed_ext` and `baseChangeHom_evaluation`
(proofs unchanged). The holes added are `podFiniteHomComparison_naturality`
(node stage3-pod-finite-hom-comparison-naturality) and
`podFiniteHomComparison_laws_remaining` (node stage3-pod-finite-hom-comparison-remaining),
in `…Base`. The holes from before are unchanged and still recorded by
lem-pod-derived-automorphism-hom-evaluation. In `…ContinuationA`:
`podIntegralHomComparison_laws`, `podRationalClosed_existsUnique`,
`podRationalHomComparison_laws`, `podCommonClosed_existsUnique`,
`podCommonHomComparison_laws`, `podSystemHomComparison_laws`,
`podFiniteRestrictionOrdinary_existsUnique`, `podOrdinaryLimitReindexing_existsUnique`,
`podLimitReindexing_existsUnique`. In `…ContinuationB`: `podReductionReindexingMap_laws`,
`podHomReductionSquare`, `podDerivedHomShift_existsUnique`,
`podFiniteHomComparison_shift`, `podFiniteHomComparison_comp`,
`podIntegralReindexedHom_shift`, `podCompletedModuleComp_existsUnique`,
`podIntegralPullbackComp_normalization`, `podIntegralHomComparison_comp`,
`podSystemNormalized`, `podSystemHomComparison_fiber`,
`podArgumentFirst_integral_rational`, `podArgumentFirst_common`,
`podRationalHomComparison_comp`, `podCommonHomComparison_comp`, and
`podIntegralRationalHomComparison_shift`.

## No longer needed

Nothing: no import, node or module was dropped.

## Where the brief, the DAG or earlier work was wrong

The original single file exceeded the 60-second per-file compile limit, so its
declarations had to be split across modules. The six existing nodes that record
declarations of the original module (def-pod-partial-closed-interfaces,
def-sf-integral-completion-transpose, def-sf-adic-closed-reindexing-maps,
def-pod-system-hom-reindexing-maps, def-sf-derived-argument-first-evaluation,
lem-pod-derived-automorphism-hom-evaluation) still name the item module, which
re-exports all of those declarations through its public import.

## New nodes

`stage3-pod-finite-hom-comparison-naturality`: naturality of the finite
evaluation-defined comparison in both arguments, proved formally by transposition,
naturality of the tensor comparison and dinaturality of evaluation.

`stage3-pod-finite-hom-comparison-remaining`: invertibility (by the
resolution-model and evaluation-calculus lemmas), and the evaluation and
transposition equations (formal, from the definition as a transpose).

`stage3-derived-automorphism-continuation-a`: extensionality of partial closed
data (`podPartialClosed_ext`), proved.

`stage3-derived-automorphism-continuation-b`: the evaluation equation of the
coefficient base-change map (`baseChangeHom_evaluation`), proved.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review. Corrected by the reviewer: the placeholder theorems `continuationA_compiles`/`continuationB_compiles : True` and their content-free nodes were replaced by the two helper lemmas and their nodes, and the two decomposition nodes were rewritten. Their stmt_deps are now the defining nodes rather than the item and an off-branch theorem, and their docstrings now carry a proof in words.
