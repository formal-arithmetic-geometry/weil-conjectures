## What changed

Proved the expression-level assembly in CompletedOperationTowerSubstitution:
primitive comparison naturality by whiskering, recursive naturality and simultaneous
substitution by induction, normalization and invertibility by induction, transition
compatibility by naturality of the actual derived transition, and StructuralLaw by
conjugation and cancellation. The final theorem eliminates the primitive-model
existence theorem and combines these proofs without changing its signature.

Extracted the six existing primitive data declarations verbatim into
Sheaf.Paper.NormalizedCompletedOperationModels, publicly re-exported from the
original module. Added PrimitiveLaws and the construction theorem
normalizedCompletedOperationModels, isolating original proof steps 1--6. The
construction theorem is strictly smaller: it says nothing about expressions,
recursive comparisons, substitution or structural transport. It is currently
unfinished; the full-calculus tensor-equality and completion-unit normalizations
are not supplied by the six newer dependency interfaces.

Change record: coord/changes/F5-completed-operation-primitive-models.md.
Its Users table now includes 871 recorded consumers, covering all
705 current downstream modules, the changed item itself and previous entries.
This repair addresses the return at head 305fcaa044e: added explicit Users rows
for AffineSpaceCoordinateBoundaries, AffineSpaceThomMap and
AffineSpaceZeroSectionPurity. Their short-name unit and tensor uses are the
finite-coefficient AffineZeroPurity.unit and AffineSpacePurity.tensor.
All three sources were inspected; none needs a Lean adaptation. Also inspected
and recorded the newly downstream
Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness, which uses no
moved primitive directly. All four modules are currently unclaimed.
The full current downstream inventory is covered, with every earlier row kept.
Only the change record and this report were edited for this return.
The delivery tool rebases the retained packet against current sheaf-dag.
Previous return repairs remain recorded in the change record.
The unit has no realized statement or proof steps to bypass. The construction
uses the same quotient/Roos route as the original proof.

## Proved and sorry left

Closed the original textual hole in
WeilConjectures.CompletedOperations.completedOperationTowerSubstitution
(node lem-pur-completed-operation-tower-substitution), conditional on the
primitive-model construction. Added one hole:
WeilConjectures.CompletedOperations.normalizedCompletedOperationModels
(node lem-pur-normalized-completed-operation-models).
This is a decomposition: one upper hole closed and one strictly smaller
construction hole added, net zero holes. The assigned module contains zero
sorry; the new module contains one. No definition contains sorry and no
arbitrary data is selected from this existence theorem in a definition.

Validation for this repair on 2026-10-22: the assigned theorem signature and
the complete moved primitive declaration block match current source verbatim.
The current source-only downstream inventory has no missing Users row.
lcompile.py --all compiled both retained modules without errors or warnings
(7.1 s for primitive models and 27.2 s for the assigned module).
The delivery also runs the required compile and preflight checks.

The six private helper proofs in the assigned module contain no sorry:
tensorComparison_naturality, pullbackComparison_naturality,
comparison_naturality, comparison_substitution,
comparisonLaws_of_primitive, structuralLaw_of_invertible.

## No longer needed

Removed the following private proof imports from the original module (the
new construction node records the genuinely needed construction dependencies):

- Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
- Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition
- Sheaf.CategoryTheory.StrictRoosComparison
- Sheaf.Paper.NormalizedDVREffectivity
- Sheaf.Paper.IntegralReductionTowerCanonical
- Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.Algebra.Homology.KFlatTotalTensorModel
- Sheaf.Paper.KFlatRingedToposPullback
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
- Sheaf.AlgebraicGeometry.ProEtaleConstantExact
- Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
- Sheaf.Paper.IntegralOperationsWellDefined
- Sheaf.Paper.NormalizedDVRTower

The assigned proof no longer needs the six intermediate dependency modules:

- Sheaf.Paper.NormalizedOperationSystemModels
  (lem-pur-normalized-operation-system-models): primitive closure remains needed
  by the construction node, rather than the expression induction.
- Sheaf.Paper.CompletedPrimitiveCounitComparison
  (lem-pur-completed-primitive-counit-comparison): primitive realization remains
  needed by the construction node; its interface does not supply full Models.
- Sheaf.Paper.FiniteExpressionReductionComparison
  (lem-pur-finite-expression-reduction-comparison): proved directly for the
  existing recursion, avoiding a second expression-evaluation interface.
- Sheaf.Paper.NormalizedTensorConstraintTransport
  (lem-pur-normalized-tensor-constraint-transport): StructuralLaw specifies the
  unique transported isomorphism, which follows by conjugation; it does not
  equate that map to a separately defined completed associator.
- Sheaf.Paper.NormalizedPullbackCompositionTransport
  (lem-pur-normalized-pullback-composition-transport): the same conjugation
  argument applies uniformly to the existing structuralValue compositor.
- Sheaf.Paper.ExpressionCounitSubstitutionCoherence
  (lem-pur-expression-counit-substitution-coherence): proved naturality and
  substitution directly for the existing recursion.

No modules are withdrawn, and these module names are claims only about this
proof's dependency needs, not global orphan status. The original seven stale
tool_uses entries are removed from the parent node; construction dependencies
remain in the new node.

## Where the brief, the DAG or earlier work was wrong

The latest return at head 305fcaa044e identified three missing Users entries.
They now have explicit rows recording the actual finite-coefficient unit and
tensor uses. The refreshed inventory also found and recorded the new
BrownHypothesesFiniteFieldCompactness consumer. All previous rows are retained.
No Lean adaptation was required. The primitive declaration block and assigned
theorem signature still match current source verbatim. Rebase is performed by
deliver3.py against current sheaf-dag.

The six newly stated dependencies use different interfaces: a semilinear
calculus and geometric coefficients, a reduction-only primitive calculus with
its own Roos realization, and separately defined expression recursions. They
do not directly supply Models, whose full calculus is constrained by equality
to the specified integral closed structure, a shared sequence duality model,
completion_unit, and simultaneous normalized pullbacks using the same Roos
models at every location. These compatibility obligations cannot be filled
by merely selecting independently existential models for each morphism.

The formal StructuralLaw is an existence-and-uniqueness characterization by
the comparison squares; conjugation and counit naturality suffice for it.
Its statement does not require identification with any independently defined
completed structural constraint. No assertion was weakened to use this route.

## New nodes

lem-pur-normalized-completed-operation-models isolates the simultaneous
primitive construction and closure from original proof steps 1--6. Its source,
complete construction proof in words, search records and Lean attachment are
provided. This node does not assert any expression or structural law. Existing
Models and its five associated primitive definitions move verbatim to its
module; public re-export preserves all consumer names and types.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
