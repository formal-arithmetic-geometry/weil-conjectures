## What changed

Proved CategoryTheory.ToposFiniteFreeCompact.scalar_exact with its original statement.
Its ordinary extension preserves finite limits by the new proved theorem
CategoryTheory.constantFiniteFree_extensionLeftExact. The normalized ordinary
coefficient adjunction supplies preservation of finite colimits. Exactness implies
that termwise extension preserves all quasi-isomorphisms; the localization universal
property then makes the specified universal derived counit invertible on all complexes.
No boundedness or extra geometric hypothesis is introduced.

The new module Sheaf.CategoryTheory.ConstantFiniteFreeExtensionLeftExact handles
independent site-object, site-morphism and coefficient universes. Its private
section-basis construction adapts the proved construction of
ConstantFiniteFreeSectionBasis using the given EssentiallySmall hypothesis. It reuses
the already proved private sheafifiedTensorIso and naturality helpers of
ConstantFiniteFreePowerIso at their independent universes. The natural finite-power
isomorphism on underlying abelian presheaves proves left exactness by reflection.
All private helper definitions are actual constructions; every helper proof is complete.

The assigned module adds private proof imports and a proved private lemma expressing
the exact-functor localization argument for arbitrary abelian categories. Local
instance priorities prefer the stored site-composition witnesses during elaboration.
Existing statements, definitions, exported attributes and public imports are unchanged. The existing node records the completed
scalar_exact argument. Change record:
coord/changes/J4-constant-finite-free-extension-left-exact.md.

Validation: the new ordinary module compiles cleanly in 23.4 seconds and the
assigned constituent module compiles cleanly in 47.7 seconds through lcompile.py.
No profiling options remain.

## Proved and sorry left

Closed one of the six original holes:
CategoryTheory.ToposFiniteFreeCompact.scalar_exact.
Added zero holes and split off zero holed statements. The new theorem
CategoryTheory.constantFiniteFree_extensionLeftExact and all its helpers are proved.

Five original holes remain unchanged, all belonging to
lem-pur-topos-finite-free-compact-constituents:

- CategoryTheory.ToposFiniteFreeCompact.tensorPullbackInv_isIso
- CategoryTheory.ToposFiniteFreeCompact.finiteFreeCompactCoordinates
- CategoryTheory.ToposFiniteFreeCompact.restrictionOpen_isIso
- CategoryTheory.ToposFiniteFreeCompact.chi_comp
- CategoryTheory.ToposFiniteFreeCompact.beta_comp

These retain their complete existing proof docstrings. The new ordinary theorem
covers the empty finite basis, the zero coefficient ring and independent universes.
The finite-power limit argument includes empty diagrams and requires no nonzero rank.

## No longer needed

No existing imports, nodes or modules are removed. The remaining constituent and
composition clauses still need their recorded proof dependencies. The completed
scalar_exact proof uses ordinary finite-free coordinates, the ordinary coefficient
adjunction and the localization universal property; it does not need K-flat
representative computations to establish invertibility of the counit.

## Where the brief, the DAG or earlier work was wrong

No statement was found false and no target or unit route changes. The existing public
constantFiniteFree_sectionBasis and constantFiniteFree_underlyingPowerIso require
a coefficient universe that is the maximum of the site universes. That signature
cannot directly instantiate the assigned scalar_exact statement, which permits an
independent coefficient universe and gives EssentiallySmall there. The new proved
ordinary theorem fills that universe gap without changing those public interfaces.

The latest purity-transport blueprint has evolved since this node's archived source;
this delivery retains the assigned general constituent statement and its finite-free
coordinate argument, rather than changing any target or blueprint-unit statement.

## New nodes

lem-pur-constant-finite-free-extension-left-exact records the proved ordinary
left-exactness theorem. It is strictly a part of scalar_exact: it involves no derived
category, universal derived functor, counit or preservation of finite colimits. Its
finite-basis proof constructs a natural finite power after forgetting to abelian
presheaves, then reflects finite limits. It has no sorry and becomes no new proof item.
Mathlib searches were run with leanfinder, loogle and grep; the imported blueprint
search found no matching blueprint node. Its statement and Lean attachment use the
original independent universe parameters.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
