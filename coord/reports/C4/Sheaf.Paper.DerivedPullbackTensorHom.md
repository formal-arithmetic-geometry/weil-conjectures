## What changed

Replaced `WeilConjectures.commonStageDerivedTensor_existsUnique`'s sorry by the
proved generic `BilinearCoefficientDescent.descent_existsUnique`, specialized to
the actual rational tensor functors, the recorded stage system, and the finite
coefficient compositum. The proof identifies the generic endpoint comparison
with `commonStageTensorComparison` and converts both directions of the complete
object and representative-map specification, including uniqueness.

Added proof-only imports of `import all Sheaf.Paper.RationalTensorStageCoherence` and
`import all Sheaf.CategoryTheory.BilinearCoefficientDescent`, together with
`import all Mathlib.Logic.Small.Defs` for the coefficient size model. The generic
family accessor bodies are needed for definitional identification. Local
elaboration settings are confined to the tensor proof. The new comparison is constructed explicitly by whiskering the normalized rational tensor
scalar comparison with the recorded transition equalities. Its remaining theorem
is the specific coefficient-tower equation; no quotient functor is assumed there.
Two private, proved categorical helpers identify its endpoint formula and convert
the generic descent record to the exact curried specification without simplifying
the concrete coefficient category. Existing signatures,
public imports and definitions are unchanged. Both delivered modules are checked
with the remote compiler in import order; all development profiling is removed.

## Proved and sorry left

Closed the body hole in `WeilConjectures.commonStageDerivedTensor_existsUnique`
(node `def-weil-derived-pullback-tensor-hom`) by reduction to a strictly smaller
coefficient-tower lemma. This is a decomposition, not a complete proof of tensor
coherence: one upper hole closed, one lower hole added, net zero holes closed.

The original item had three holes. Two are left, unchanged:

- `WeilConjectures.commonStagePullback_comparison_data`
  (`lem-weil-common-stage-pullback-comparison-data`).
- `WeilConjectures.commonStageDerivedInternalHom_existsUnique`
  (`def-weil-derived-pullback-tensor-hom`).

One hole is added in the new module:

- `WeilConjectures.rationalTensorStageComparison_coherent`
  (`lem-weil-rational-tensor-stage-coherence`). Its docstring and node give the
  completion-conjugation and rational-localization proof from the existing
  ordinary coefficient-tower equation. It asserts only the stage comparison
  equation, with no common-stage functor, object formula or quotient arrow formula.

## No longer needed

None. No existing import or node was removed. Generic bilinear descent replaces
rewriting the quotient construction, transport independence, functor laws and
uniqueness in this module. The coefficient tower calculation remains needed.
The source-library declarations and their dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The previous DAG's final step grouped the unfinished tensor and internal-Hom
arguments without an explicit tensor proof dependency. The delivery records
that tensor descent uses the existing generic bilinear descent theorem and the
specific remaining scalar-tower equation.

The current blueprint file is under
`literature/blueprint/latest/blueprint/sec-proetale-coefficients/sk-prop-sf-open-closed-triangle/`;
the older path in the live node no longer exists in that snapshot. The current
blueprint states ambient condensed-ring operations, while the assigned live
module retains legacy constructible common-stage operations and their exact
normalizations. This delivery preserves those existing interfaces and supplies
a genuine step in their stated tensor argument; it does not purport to resolve
that pre-existing blueprint/interface discrepancy.

## New nodes

`lem-weil-rational-tensor-stage-coherence` in
`dag/nodes/sec-smooth-purity/lem-weil-rational-tensor-stage-coherence.json` attaches
the explicit normalized stage comparison and its coefficient-tower equation in
`Sheaf.Paper.RationalTensorStageCoherence`. The statement covers arbitrary schemes
with the existing invertibility hypotheses, repeated fields, identity inclusions,
zero objects and empty schemes. Its proof is the ordinary tower equation followed
by completion conjugation, restriction, rationalization, and the recorded
transition/associator equalities. No change record is needed: no existing
statement, definition or public import was changed.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
