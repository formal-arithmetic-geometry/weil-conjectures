## What changed

The assigned theorem section_resolving_oplax_constraint_diagrams now has a complete
Lean assembly proof, with its original signature. The proof explicitly composes
the six associativity edge squares, retains their common outside vertex maps,
uses section_oplax_total_comparison for the ordinary cochain associator equation,
and cancels the final invertible comparison. The two unit diagrams are assembled
in the same way from their three edge squares and opposite branches, using the
ordinary left and right cochain unit equations.

The private helpers paths_of_edges and units_of_edges prove these compositions
for arbitrary monoidal categories. The private helper
section_vertices_of_resolving proves all six vertex isomorphisms directly:
one-sided invertibility of qTensor suffices for every binary tensor map, and the
specified ε is already the hom of mapDerivedCategoryFactors, a natural
isomorphism for the exact section pullback.

Three remaining calculations are separate public theorems: resolving closure
and the six model edge squares, regular-unit edge squares, and the final internal
conjugation assertion. The common definitions moved verbatim to
Sheaf.Paper.SectionResolvingOplaxConstraintData, publicly re-exported by the
original module, so the independent proof modules have no circular imports.
UnitEdgeIdentification and SectionUnitEdges extract only unit vertex/edge data;
whole-path formulas and path equality are proved in the main file. All forty
original declaration signatures are preserved, and no source-library file or
target statement is edited.

Change record: coord/changes/H7-resolving-oplax-data-and-edges.md.

All five delivered Lean modules compiled through lcompile.py. The final successful
compile took 26.4 seconds for the assigned module; the four support modules took
3.3, 6.3, 6.5, and 6.9 seconds. There were no warnings or errors. Delivery preflight
will independently run its compile and axiom checks.

## Proved and sorry left

Original holes: 1. The original hole in
AlgebraicGeometry.ProEtale.ModuleRingedComparison.ResolvingOplaxConstraints.section_resolving_oplax_constraint_diagrams
is discharged by the assembly proof. This is a decomposition, not a complete
proof of the mathematics: three strictly smaller named holes are added. The
assigned module and the shared data module contain zero holes. Net hole count
for this delivery: 1 closed minus 3 added = -2.

The three new holes, and every sorry left in the delivery, are:

- AlgebraicGeometry.ProEtale.ModuleRingedComparison.ResolvingOplaxConstraints.section_resolving_oplax_model_edges,
  node lem-pd-section-resolving-oplax-model-edges, in
  Sheaf.Paper.SectionResolvingOplaxModelEdges.
- AlgebraicGeometry.ProEtale.ModuleRingedComparison.ResolvingOplaxConstraints.section_resolving_oplax_unit_models,
  node lem-pd-section-resolving-oplax-unit-models, in
  Sheaf.Paper.SectionResolvingOplaxUnitModels.
- AlgebraicGeometry.ProEtale.ModuleRingedComparison.ResolvingOplaxConstraints.section_resolving_oplax_internal_conjugation,
  node lem-pd-section-resolving-oplax-internal-conjugation, in
  Sheaf.Paper.SectionResolvingOplaxInternalConjugation.

The proved private helpers are paths_of_edges, units_of_edges, and
section_vertices_of_resolving. No sorry occurs inside a definition, a private
helper, or a partial proof. Each new hole is exactly a named public theorem with
`:= by sorry`, its source and proof in words, and its own DAG node.

## No longer needed

The original private import
Sheaf.Paper.DerivedPullbackRepresentativeComputation and the planned direct use
of lem-weil-pbc-kflat-tensor-pullback-computation-universes are unnecessary for
this proof. The actual ε used in the existing Lean statement is a component of
a natural isomorphism on all complexes, so no separate resolving counit
invertibility theorem is required.

The original private imports Sheaf.Algebra.Homology.KFlatTotalTensorModel and
Sheaf.Paper.KFlatRingedToposPullback move to the model-edge obligation where their
closure and preservation statements are needed. The latter is also used in the
unit-edge plan. The parent no longer directly uses these nodes or
lem-weil-pbc-site-derived-tensor-descent; those still serve the smaller edge
obligations. The parent's four obsolete top-level tool_uses approvals are
removed. The new nodes request the inherited generic tool uses in their
split_report.tool_uses; the independent reviewer can approve them there.

All original public imports move unchanged into the shared data module; the
original module publicly re-exports them. No entire module or DAG node is
withdrawn or claimed globally unused. The original unfinished parent still cites
the assigned theorem, despite its having zero current Lean importers. The unit's
realized route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan used the general K-flat derived-pullback computation to establish
ε invertibility. For this exact section pullback, the existing Lean ε is already
mapDerivedCategoryFactors.hom, so its invertibility is supplied directly by its
natural isomorphism. This shortens that part of the argument. No statement was
found false or weakened.

The monoidal structure in the statement is the explicitly transported one,
derivedMonoidal. The proof installs this structure locally; using the ambient
native derived monoidal instance instead gives a genuine instance mismatch.

The combined theorem's generic and specialized diagram data initially lived in
the same file as its proof obligation. Independent split modules could not import
that file without a cycle, so the unchanged data now has a separate owner node.
No second-reader section is included, as instructed for dispatcher workers.

Edge cases checked against the definitions and sources: identity pullback, zero
complexes and zero coefficient ring, the degree-zero regular unit, and unbounded
triples. No nonzero-object, boundedness or tensor-of-two-resolving-factor
assumption was introduced. Vertex invertibility only uses one resolving tensor
factor at a time. Internal conjugation keeps the given γ, θ and regular unit;
it introduces no chosen witnesses or endpoint maps.

## New nodes

- def-pd-section-resolving-oplax-constraint-data owns the shared, unchanged diagram
  data and the two new edge-only unit predicates in
  Sheaf.Paper.SectionResolvingOplaxConstraintData. It is a definition node with
  zero holes. The original node retains only its theorem attachment.
- lem-pd-section-resolving-oplax-model-edges covers original Steps 1–6 and the
  target-associator square of Step 7, with resolving closure and all six edge
  squares. It omits vertex invertibility and all whole-path conclusions, which
  are proved in the parent.
- lem-pd-section-resolving-oplax-unit-models covers the vertex isomorphisms and
  individual unit edge squares in original Steps 9–10. It omits all four full-path
  conclusions; the parent proves those from the ordinary cochain unit equations.
- lem-pd-section-resolving-oplax-internal-conjugation covers original Steps 11–12.
  Its proof plan derives all-object section unit equations from the smaller unit
  edge theorem via resolving localization before applying the fixed conjugation.

Every new statement is strictly part of the original argument. Their statements,
source references, natural-language proof steps, dependency unions and actual
Lean signatures are recorded in the new nodes. Mathlib and whole-blueprint
searches found generic monoidal tools but no duplicate specified-map statement.
The existing parent node's proof, proof_deps, proof_origin and Lean declaration
ownership now follow the Lean assembly. The original statement and stmt_deps,
and the unit record, stay unchanged.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
