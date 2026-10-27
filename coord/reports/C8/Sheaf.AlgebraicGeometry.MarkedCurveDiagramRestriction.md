## What changed

Proved `AlgebraicGeometry.exists_marked_curve_diagram_restriction` in
`Sheaf.AlgebraicGeometry.MarkedCurveDiagramRestriction` without changing its signature.
The proof constructs the base open and every scheme and arrow by restrictions or
pullbacks. Two proved private helpers handle induced pullback arrows and fibre transport.
Added the proof-only import `WeilConjectures.AlgebraicGeometry.Curve.GenericModelAux`
for its proved cartesian coproduct and open-restriction lemmas. Updated the existing
node's proof and proof origin to describe the actual Lean construction.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.exists_marked_curve_diagram_restriction`
(node `lem-weil-pbc-marked-curve-diagram-restriction`). Added zero holes and zero
split statements. There is no `sorry` left in the delivered Lean file. Both private
helpers are proved. Empty component families and empty schemes are covered by the
same coproduct and pullback constructions; no nonemptiness assumptions were added.

## No longer needed

None. All four existing declared proof dependencies remain used, through their
Mathlib permanence instances or the thickening definition. No existing import was
removed, and no module or node is withdrawn. No generic-fibre spreading or descent
lemma is used directly by this proof.

## Where the brief, the DAG or earlier work was wrong

No false statement or route error was found. The original single proof paragraph
omitted substantial cartesian glue; the node copy now records the actual steps.
The source module has two already-proved general lemmas which supply coproduct
base change and open restriction, so no new split-off obligation is necessary.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
