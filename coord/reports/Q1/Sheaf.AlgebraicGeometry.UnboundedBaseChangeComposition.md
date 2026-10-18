## What changed

Proved both theorems of `Sheaf.AlgebraicGeometry.UnboundedBaseChangeComposition`, with their
existing signatures unchanged. Three proved private helpers derive the unbounded horizontal
pasting formula from the source library's pullback-composition coherence and the generic
mate-pasting and mate-whiskering laws. The degreewise proof applies the existing exact
pullback/cohomology and single-sheaf comparison isomorphisms, then naturality and functoriality.

Added the proof-only import
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence`.
The three public imports are unchanged. No definitions, public signatures, or consumers change.
Updated the node's proof, proof dependencies, proof origin, and obsolete tool uses to describe
this direct source-library route. The unit `sk-def-bc` has no realized statement or steps to bypass.

## Proved and sorry left

Closed both original holes (node `sbc-lem-base-change-composition`):

- `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_of_cartesian_tower`.
- `AlgebraicGeometry.Etale.isIso_homology_derivedBaseChangeMap_of_cartesian_tower`.

Holes closed: 2. Holes added: 0. Holes left in the delivered Lean module: 0.
No split-offs and no new axioms. All three private helper theorems are proved.

## No longer needed

Removed seven proof imports:

- `Sheaf.AlgebraicGeometry.DerivedSquareIsoPasting`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`.
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`.
- `Mathlib.CategoryTheory.Localization.Predicate`.
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.

The proof no longer needs the declared proof dependencies
`lem-weil-pbc-cartesian-square-pasting`, `lem-weil-pbc-inverse-image-composition`,
`lem-weil-pbc-derived-square-iso-pasting`, `prop-weil-pbc-inverse-image-exact`,
`def-weil-pbc-derived-square-iso`, `lem-weil-pbc-localization-universal-property`,
`def-kun-unbounded-exchange`, `sbc-def-base-change-map`, and `def-weil-pbc-direct-image`.
All corresponding obsolete top-level tool-use entries are removed, preserving the two
remaining entries in their original order.

The source library already supplies unbounded pullback composition coherence, exactness
comparisons with homology, and the singleFunctor comparison. Applying these is shorter than
proving those facts again through termwise localization. Cartesian pasting is unnecessary:
the private pasting calculation works for arbitrary commutative squares. The canonical
module-coefficient exchange in the statement is already defined in the unchanged public
`DerivedUnbounded` import, so neither alternative abelian exchange construction is used.
These are dependencies pruned from this item's proof, not claims that globally shared source
modules can be deleted. No module is withdrawn. The change record is `coord/changes/UnboundedBaseChangeComposition.md`.

## Where the brief, the DAG or earlier work was wrong

The named `derivedSquareIsoPasting` and `derivedExchange_identity_pasting` interfaces concern
bounded-below categories with AddCommGrpCat coefficients. They do not directly specialize to
the item's unbounded ModuleCat statement. The source library's newer unbounded
`UpperStarCompCoherence` and exact-pullback comparison API provide the needed laws without
changing any interface. The actual Stacks 0EZS diagram has arrows pointing left, as in the
Lean statement; the blueprint_update rendering points right, but no statement is changed.

Read Stacks `etale-cohomology.tex`, label `lemma-base-change-compose`, and
`sites-cohomology.tex`, label `remark-compose-base-change-horizontal`. Checked the proof
against both the unbounded and single-degree assertions. Identity squares, zero sheaves,
and q=0 require no special cases; the proof uses only isomorphism functoriality and makes no
properness, torsion, or boundedness assumption.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
