## What changed

Proved `AlgebraicGeometry.ProEtale.comparisonCohomologyMap_bijective` in the item
module. The proof uses the existing Grothendieck-abelian comparison unit, the existing
arbitrary-coefficient injective acyclicity theorem, and the existing bounded-below
derived-unit criterion. A private Ext-to-derived-Hom bridge converts full faithfulness of
the bounded-below comparison functor into bijectivity of `mapExtAddHom`; the unchanged
constant-sheaf precomposition then gives the specified map. Removed proof-only imports
of site Leray, site cohomology pullback, abelian pullback exactness, long exact sequence,
and comparison pullback sections.

## Proved and sorry left

Closed the only sorry in the item: `AlgebraicGeometry.ProEtale.comparisonCohomologyMap_bijective`.
No sorry was added. The new DAG node records the already proved generic derived-unit
criterion used as a dependency; it adds no Lean sorry or module.

## No longer needed

The proof does not need the modules `Sheaf.CategoryTheory.SiteCohomologyPullback`, `Sheaf.CategoryTheory.SiteLerayDegenerate`,
`Sheaf.CategoryTheory.SitePullbackAbelianExact`, and
`WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`, nor their nodes
`lem-weil-pbc-site-cohomology-pullback` and `lem-weil-pbc-site-leray-degenerate`. The
unit-route imports `Sheaf.CategoryTheory.SiteCoveringAxioms` and
`Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections` remain retained even though
the shorter proof does not use their declarations.

## Where the brief, the DAG or earlier work was wrong

The original proof plan routed through an existential Leray edge map and then required a
separate naturality proof identifying that edge with `comparisonCohomologyMap`. The existing
exact comparison adjunction gives a shorter route: its derived unit is invertible on all
bounded-below objects once injective images are acyclic, so full faithfulness directly proves
bijectivity of the canonical Ext map. The target statement and both public definitions are
unchanged.

## New nodes

`lem-cbc-derived-unit-injective-acyclicity` records the existing declaration
`CategoryTheory.Adjunction.isIso_derivedPlus_unit_app_of_rightAcyclic` in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic`.
Its statement is strictly the derived-unit sub-lemma used by the item and introduces no new
Lean file or sorry.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
