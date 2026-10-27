## What changed

Replaced the body of AlgebraicGeometry.exists_spread_marked_curve_diagram by an explicit
assembly of diagram descent and final shrinking. Its statement and all original public
imports remain unchanged. The proof lifts each of the three supplied generic comparison
maps through the restriction pullback square; pullback cancellation proves the new squares,
and cancellation of the open comparison immersions proves compatibility with j₀ and q₀.

Added three modules:

- MarkedCurveDiagramModel: descent and the marked thickening before the final shrinking;
  its good-fibre and marked-image conditions are required only above η.
- MarkedCurveDiagramRefinement: chooses a common neighbourhood where those conditions
  hold everywhere. This proof is complete: geometric connectedness is open for the proper
  smooth p_i, the dimension bound is open by upper semicontinuity, and the marked image
  is open by smoothness. Apply the existing finite-image shrinking theorem directly to
  T_i→V→U, then restrict the diagram.
- MarkedCurveDiagramRestriction: transports an existing marked diagram under a specified
  base restriction and records all cartesian comparisons. This is independent of generic
  field descent and does not choose a good-fibre neighbourhood.

All additions are under Sheaf. No adopted source module, target statement, existing public
signature, or definition changed. The only new data constructions are explicit pullback
lifts inside proofs. Nothing is chosen from an unproved existence theorem in a definition.

Validation: the main assembly and refinement compiled together through lcompile.py,
against the two named intermediate interfaces. The explicit restriction proof attempt
has remaining compiler errors and is retained only in sandbox scratchpad, outside the
delivery. Its submitted theorem body is exactly `by sorry`. Final packet compilation
and preflight are performed by deliver3.py.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.exists_spread_marked_curve_diagram (1 of 1 original bodies).
Its replacement proof is complete relative to its explicitly named dependencies.
Also proved AlgebraicGeometry.exists_marked_curve_diagram_refinement and the private
helper AlgebraicGeometry.lift_generic_square_through_refinement.

Remaining split obligations:

- AlgebraicGeometry.exists_marked_curve_diagram_model,
  node lem-weil-pbc-marked-curve-diagram-model: model descent and generic conditions.
- AlgebraicGeometry.exists_marked_curve_diagram_restriction,
  node lem-weil-pbc-marked-curve-diagram-restriction: transport under a specified open.

Thus this is a decomposition, not a complete proof: one original hole closed and two
strictly smaller holes added. There are no holes inside definitions or private lemmas.
The assigned module and the refinement module have zero local holes.
Actual packet hole count: 2. This is a decomposition with net hole change +1, not
a net reduction in the targets’ import closure.

## No longer needed

No original public import was removed. No module or declaration is withdrawn.
The assigned theorem now directly uses only the two new nodes for model descent and
refinement. The old proof dependencies remain below those nodes where their mathematics
is needed; this is a relocation of dependencies, not their pruning.

Two former implementation dependencies are not needed for this route:

- lem-weil-pbc-localization-colimit-principal-localizations,
  WeilConjectures.RingTheory.LocalizationColimitPrincipalLocalizations;
- lem-weil-pbc-limit-affine-transition, WeilConjectures.AlgebraicGeometry.LimitAffineTransition.

The model-descent plan uses the already proved affine-neighbourhood stalk limit instead
of constructing a principal-localization diagram. The final shrinking proof applies the
finite-image neighbourhood theorem to the composites T_i→V→U. It does not separately
shrink V and then descend that shrinking through the radicial cover. No unsupported
whole-library reachability claim is made for any of these modules.

## Where the brief, the DAG or earlier work was wrong

No false statement or mathematical obstruction was found. The original theorem's
signature is preserved. The previous single obligation combined finite diagram descent,
marked-open descent, neighbourhood selection and cartesian transport. The current split
separates these tasks and actually proves the neighbourhood selection and generic-map
transport; it does not rename the original obligation.

The elementary neighbourhood argument is shorter over U: each T_i→V→U is finite, so
one application of the proved finite-image theorem suffices. Neither a unique-point
argument for V nor a second shrinking step is necessary at that point.

New interfaces were checked against the empty family, empty schemes, nonreduced bases,
and fibres outside the chosen neighbourhood. The restriction lemma assumes the good
conditions throughout the specified open, while the model lemma requires them only
above η. The latter does not assert global connectedness, dimension bounds, or marked
surjectivity. The refinement derives those missing conclusions from actual openness.

## New nodes

lem-weil-pbc-marked-curve-diagram-model, module MarkedCurveDiagramModel: the descent
portion of Tag 0GK7, ending with the marked thickening and conditions at points over η.
It is strictly less than the assigned statement: it has no global fibre properties or
surjectivity of the marked opens, and those cannot be inferred without a further shrinking.

lem-weil-pbc-marked-curve-diagram-refinement, module MarkedCurveDiagramRefinement:
proved common-neighbourhood selection and application of restriction. It starts with
an existing diagram over schemes; it contains no field-extension or model descent.

lem-weil-pbc-marked-curve-diagram-restriction, module MarkedCurveDiagramRestriction:
transport under a specified good base open, including comparisons preserving independently
supplied generic diagrams. It performs no descent and no neighbourhood selection.

The new nodes have their Lean statements, Tag 0GK7 source, proof in words, and three
kinds of Mathlib searches. The blueprint ancestor tool returned None for a node created
for this non-blueprint item; the new nodes retain that null ancestor and record the item
in the via list. The unit and chapter route is unchanged. There are no existing-interface
changes requiring a consumer adaptation or a change record.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
