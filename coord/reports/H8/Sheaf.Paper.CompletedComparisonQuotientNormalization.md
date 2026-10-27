## What changed

Replaced the assigned assembly hole by a direct constructor-induction proof for the prescribed ordinary quotient complexes. The proof establishes system and finite-level goodness, normalized transitions, invertibility of recursive substitutions and their specified counit reductions, and naturality for simultaneous compatible representative and derived-input maps. The existing theorem signature is unchanged. Private proof imports supply the existing flatness, total-tensor-map, reconstruction and intrinsic-completeness APIs. Added one module for the single-representative reduction-presentation equations, and updated the item node to record the actual proof route.

The final item module passed `lcompile.py` without warnings in 58.3 seconds after removing profiling and an unnecessary private import of Mathlib limit internals. The new presentation module compiled separately and in the sandbox import-order check. The full theorem signature was compared textually with the repository version and is identical. A local unused-variable linter option preserves the fixed existential binder `invertible`; no compiler or kernel check is disabled. The actual comparison maps and all shared definitions are unchanged.

## Proved and sorry left

Closed the original hole in `WeilConjectures.CompletedQuotient.completedComparisonQuotientNormalization` (node `lem-pur-completed-comparison-quotient-normalization`), conditional on the existing stated dependencies and the one new lemma below.

Added one hole: `WeilConjectures.CompletedQuotient.completedQuotientReductionPresentation` (node `lem-pur-completed-quotient-reduction-presentation`). It asserts only the two fixed comparison/evaluation/transition equations for one arbitrary flat-term K-flat representative on one scheme. It has no expression syntax, constructible inputs, composable morphisms, substitution, invertibility or naturality conclusion. This delivery is a decomposition: one upper hole closed, one strictly narrower hole added; zero net holes closed. No sorry remains in the item module. All private helpers are proved.

## No longer needed

The proof does not apply `completedOperationTowerSubstitution` or `completedPrimitiveCounitComparison`; constructor induction directly uses the exact maps fixed by the item definitions. It replaces the existential choice of towers in `quotientExpressionKFlatNormalization` by `quotientExpressionKFlatOperations` applied to the prescribed ordinary quotient towers. It uses unrestricted normalized reconstruction directly rather than the more restrictive actual-reconstruction wrapper from the old plan. The item DAG removes those superseded direct proof dependencies. Specifically these are `lem-pur-completed-operation-tower-substitution` (`Sheaf.Paper.CompletedOperationTowerSubstitution`), `lem-pur-completed-primitive-counit-comparison` (`Sheaf.Paper.CompletedPrimitiveCounitComparison`), and `lem-pur-normalized-actual-reconstruction-maps` (the stronger wrapper in the still-used `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`). The normalization node remains a dependency because its operations theorem is used. These modules remain present and may remain transitively imported by the unchanged public definitions; no claim of whole-library withdrawal is made. No existing public import, declaration or module is removed.

## Where the brief, the DAG or earlier work was wrong

The old plan's existential quotient-normalization theorem alone does not identify its chosen input towers with the fixed ordinary quotient complexes in this theorem. Its underlying operations theorem does apply after the prescribed finite evaluation/transition identifications. The missing fixed-presentation compatibility is therefore isolated as a single-input lemma, rather than assuming equality of two independently chosen presentations. No target, definition or existing statement is changed.

## New nodes

`lem-pur-completed-quotient-reduction-presentation`, in `Sheaf.Paper.CompletedQuotientReductionPresentation`, records the two presentation equations for the actual quotient complex and the already fixed coherent reduction and ordinary evaluation isomorphisms. Its docstring and node give the adjunction-transpose proof, including zero complexes, exponent-one quotients, and identity transitions. No change record is required: no existing interface is changed.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
