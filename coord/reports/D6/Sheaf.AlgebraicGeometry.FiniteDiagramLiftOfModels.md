## What changed

Withdrew the unused duplicate `Sheaf.AlgebraicGeometry.FiniteDiagramLiftOfModels`
under brief step 8d. Its DAG node `lem-weil-pbc-finite-diagram-lift-of-models` now
points to the existing proved declaration
`AlgebraicGeometry.finite_diagram_lift_of_models` in
`WeilConjectures.AlgebraicGeometry.FiniteDiagramLiftOfModels`.
The existing four-step proof route and its proof dependencies are retained.
Corrected the first proof step's stale reference to two private helpers: the
comparison calculation is actually local `hK` in the retained upstream proof.
No upstream source, definition, target signature, or consumer is changed.

The upstream theorem has exactly the same hypotheses, prescribed-object equations,
and path-relation equations. It packages the natural isomorphism in `Nonempty`
instead of an existential binder. A compiled scratch theorem reproduces the exact
original signature by destructuring that `Nonempty` and introducing the original
existential witnesses. No mathematical content is lost.

Change record: `coord/changes/finite-diagram-lift-upstream-dedup.md`.

## Proved and sorry left

Holes closed: 0 of 0. Holes added: 0. Split off: 0. No remaining `sorry` in the item.
The assigned shared copy was already fully proved and compiled in 12.4 seconds.
The retained upstream theorem and the scratch proof of the exact original statement
use only `propext`, `Classical.choice`, and `Quot.sound`, as checked with `#print axioms`.
This delivery prunes a duplicate; it does not claim a newly closed proof hole.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.FiniteDiagramLiftOfModels`, including its
private `finite_generators_lift` and `finite_morphism_equalities_lift` copies.
`tools/downstream.py` reports zero downstream modules, and a complete library source
search finds no importing module. There are therefore no consumer imports to adapt.
The retained upstream module contains the proved helpers and the four-step argument.

The withdrawn module's imports of
`Mathlib.AlgebraicGeometry.AffineTransitionLimit`,
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
`Mathlib.CategoryTheory.Comma.Over.Pullback`,
`Mathlib.CategoryTheory.PathCategory.Basic`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` disappear with it.
These remain used by the upstream proof; none is claimed globally unnecessary.
No mathematical DAG node is pruned. Dependencies `thm-pd-spreading-out` and
`def-pc-fibre-product` stay. The unit's realized statement/step lists are empty;
no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an unfinished theorem, but this item is listed
as `retire:Sheaf.AlgebraicGeometry.FiniteDiagramLiftOfModels` in
`coord/retire-items.tsv`. The human retirement hand-off in
`coord/changes/retire-sheaf-twins-20261020.md` explicitly requests switching to the
upstream twin and deleting the copy. The earlier M1 delivery had already proved
the theorem, so its actual starting hole count is zero. The upstream proof has
equivalent `Nonempty` packaging. The inventory lists two historical consumers:
`Sheaf.TraceFormula.StableCurveDiagramNoetherianModel` is absent in the shared tree,
and `WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent` no longer imports or
uses this module. Thus no current consumer adaptation is needed.

Searches through `msearch.py` used LeanFinder for finite diagram lifting, Loogle
for `CategoryTheory.Paths.lift`, and grep for `exists_pullback.*isLimit`.
LeanFinder returned inverse-limit single-map results and unrelated light diagrams;
Loogle returned the expected path-extension API; grep returned no additional match.
Local library search found the exact upstream theorem. No new result is needed.
Empty vertex, generator, and relation types remain included by the unchanged
hypotheses and the retained common-refinement/path-induction proof.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
