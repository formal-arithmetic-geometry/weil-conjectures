## What changed

Replaced the sole proof hole in
`AlgebraicGeometry.ProEtale.isIso_comparisonGlobalSections` by the canonical
bounded-below derived-unit argument. The finite-level proposition gives the
underived unit on injectives and positive direct-image vanishing. Applying
`Adjunction.isIso_derivedPlus_unit_app_of_rightAcyclic` pointwise makes the actual
derived unit invertible. Unfolding `comparisonGlobalSections` then expresses it
as a composition of whiskered isomorphisms, compatibility isomorphisms, and the
canonical terminal-object Leray isomorphism; Lean's `IsIso` instances finish.

Added the proof-only import
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic`.
The definition, statements, visibility and existing public imports are unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.isIso_comparisonGlobalSections`
(blueprint: `lem-weil-pbc-comparison-global-cohomology`).
No holes are added or split off. There are no remaining `sorry` declarations in
the delivered module. The proof uses the existing finite-level comparison
proposition and the generic acyclic derived-unit theorem.

## No longer needed

Removed the interrupted attempt's proof imports of
`Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison` and
`Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized`.
Neither is needed: the proof directly assembles the derived-unit and Leray route
already described by this module's docstring. They were sandbox-only imports,
so no baseline library import is removed, and no module is claimed globally pruned.
All baseline public imports are retained as the existing exported interface.
No blueprint unit statement or step is bypassed.

The current node's alternative normalized-evaluation route uses
`src-weil-pbc-comparison-global-sections-vanishing`,
`src-right-derived-functor-plus-base-change-of-right-acyclic`, and
`lemma-weil-pbc-leray-acyclicity`. This legacy module instead uses the Leray
isomorphism directly after the actual derived unit. Those alternative nodes are
not newly needed by this proof; their existing normalized theorem remains intact.

## Where the brief, the DAG or earlier work was wrong

The main-20261015 statement and proof were read: they use exactly the derived
unit followed by the terminal-object Leray comparison. The current DAG node
`lem-weil-pbc-comparison-global-cohomology` is attached to
`ComparisonGlobalCohomologyFiniteNormalized.isIso_finiteComparisonGlobalSections`,
which has already been proved by F1. The dispatched legacy module still has its
own independent proof hole and one direct importer, `Sheaf.Paper.PurityRelativeKummer`.
This delivery closes that hole without replacing the current node attachment or
changing F1's proof plan. No definition or statement repair is necessary.

The interrupted sandbox proof tried to simplify the separately named general
comparison transformation, but did not unfold that transformation's definition.
The replacement uses the finite-level ingredients directly and avoids that
additional import and definitional-equality obligation.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
