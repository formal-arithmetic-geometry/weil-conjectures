## What changed

Proved `AlgebraicGeometry.Scheme.ExactPullbackNormalization.completed_pullback_mate_factorization`
with its existing signature and all four definitions unchanged. The proof imports
`SfCompletedAugmentationAdjunct` and `ExactTowerAugmentedCounitEvaluation` as the current DAG
requires. A proved private generic adjunction calculation moves the completion unit through
the target unit and constant comparison, then uses counit naturality and the triangle identity.
The three projection/transition clauses specialize the existing augmented-counit theorem;
naturality is the existing augmentation-adjunct naturality clause.

The proof also imports all of `Sheaf.Paper.CompletedDirectImageLimits` to reuse its proved
private `derivedCounit_unit`, `constantEvaluationIso`, and `limitCounitProjection_eq` helpers.
This is a proof tool from `prop-weil-pbc-direct-image-limits`, recorded in the updated DAG;
the maintainer can record any additional cross-unit tool approval. The helper equality fixes
the actual published projection, rather than choosing a new projection or adjunction.
The private complex-unit construction is exactly the existing derived unit evaluated on the
homotopy quotient; its right-derived property is proved using the K-injective derivability
structure and `completedRlim_computation`. No data is chosen from an existence theorem.

Validation: the complete module compiled through lcompile.py with no warnings and no holes.
The edge cases of zero augmentation, equal transition indices, and arbitrary unbounded inputs
are included by the generic adjunction identities and the existing universally quantified
evaluation theorem. No completeness or product-preservation assumption is added.

Search: LeanFinder returned generic mate/counit identities; Loogle found
`Adjunction.left_triangle_components`; msearch grep and local rg found no theorem already
stating this whole result. Local search found the proved projection-normalization helpers,
which are reused directly. No new public statement is needed.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Scheme.ExactPullbackNormalization.completed_pullback_mate_factorization`
(node `lem-sf-completed-pullback-mate-factorization`). Added 0 holes; split off 0 statements.
There is no `sorry` left in any delivered Lean file. The existing theorem dependencies
`completed_augmentation_adjunct` and `exact_tower_augmented_counit_evaluation` remain separate
stage-3 items; their proofs were not changed or counted as closed.

## No longer needed

Removed the two direct proof imports `Sheaf.CategoryTheory.DerivedTowerCounitProjections`
and `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients` from the item.
Their mathematical results remain needed through the existing augmentation and evaluation
lemmas, so neither corresponding node nor module is withdrawn. No existing public import is
changed. All current declared mathematical dependencies are retained; no module is pruned.
The definitions of the adic quotient tower and the inverse-system convention enter through
the specialized augmentation and transition maps, as in the stated route.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The current DAG's two declared intermediate results suffice.
The actual projection normalization needs the already proved private helpers from
CompletedDirectImageLimits to instantiate the general evaluation theorem. This additional
proof dependency is now explicit. The theorem docstring still describes the same argument.
The unit route is preserved. No source-library declaration, target statement, definition,
instance, or public signature is changed.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
