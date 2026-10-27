## What changed

Replaced the remaining proof hole in `Sheaf.Paper.InternalHomDualConstructibleModels`
by a generic assembly and its six canonical coefficient specializations. Existing public
statements, definitions, instances, docstrings and public imports are unchanged.

The assembly proves scalar homology finite presentation using Mathlib's explicit
kernel/quotient homology model, proves reversed dual term bounds and dual term finiteness,
and composes exact pullback, derived homology factorization and exact scalar-realization
homology isomorphisms on every original chart. Exactness and Noetherianity come from
`AdmissibleScalarRealization.admissible_scalar_realization_exact`; finite-type geometry
supplies local Noetherianity and quasi-compactness. The finite coefficient nilpotence
hypothesis is converted to the annihilation hypothesis of that exactness theorem.

Two new modules isolate the remaining presentation comparisons:
`OrdinaryScalarPerfectLocalDual` transports the existing sectionwise scalar-perfect dual
computation to the item's canonical internal-module realization and original cover;
`OrdinaryScalarModelBoundedDescent` transports ordinary scalar models to the existing
finite-cover cohomology-descent interface and makes the bounds uniform by finite refinement.
The item node now records precisely this assembly. Change record:
`coord/changes/B9-internal-hom-dual-model-assembly.md`.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.ProEtale.InternalHomDualModels.internalHomDual_constructible_models`
(`lem-sfb-internal-hom-dual-constructible-models`). Its proof has no direct `sorry`.

New proved private helpers:
`finitePresentation_homology` and `assertion_of_exact_realization` in the item's namespace.

Two holes added, each the entire proof of a public named theorem in a separate module:

- `AlgebraicGeometry.ProEtale.ordinaryScalarPerfect_local_dual`
  (`lem-sfb-ordinary-scalar-perfect-local-dual`). This gives only the dual's local derived
  representative, for any topological ring; it says nothing about finite presentation,
  the original object's cohomology, or either object's global constructibility.
- `AlgebraicGeometry.ProEtale.ordinaryScalarModel_bounded_descent`
  (`lem-sfb-ordinary-scalar-model-bounded-descent`). This gives Dbc for one object from
  exact scalar models with already finitely presented cohomology. It has no internal Hom,
  projectivity, coefficient classification or original-chart cohomology formulas.

This is a decomposition of the one remaining hole, not a completed proof of the mathematical
assertion: 1 hole closed, 2 added, 0 direct holes left in the item, 2 direct holes in the
packet. The theorem still depends on these holes. No new data definition uses `sorry`.

## No longer needed

No module is withdrawn or claimed globally pruned. No existing public import is removed.
The three new private proof imports are the exactness theorem and the two new lemmas;
Mathlib proof imports provide scalar homology and finite-type geometry.

The item's previous direct citations to scalar-perfect dual realization and ringed Hom
restriction now occur in the local-dual node. Its previous direct citations to finite affine
refinement, coefficient localization, exact slice restriction, locally Noetherian
quasi-separatedness and local-model cohomology descent occur in the descent node (and,
where appropriate, in the local-dual node). They remain mathematically needed; these are
relocated obligations, not pruned work. Scalar dual finiteness, Noetherian finite
kernels/quotients, finite presentation, exact-functor homology, coefficient exactness and
finite-type geometry remain direct dependencies of the item. Unit routes are unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned conclusions are true, but the attached Lean interfaces do not compose by
simple specialization. `ScalarPerfectDualRealization` uses sectionwise module sheaves
on a site small in its module universe; the item uses internal abelian sheaf modules
with separate site and coefficient universes. The comparison must transport the scalar
realization, ordinary dual coordinates, unit, and derived Hom, with suitable universe
transport. Also `localModel_cohomology_descent` accepts internal modules over the
point-section scalar ring and a finite cover with one fixed interval, while the item
starts with ordinary scalar modules and an arbitrary cover with memberwise intervals.
The new statements isolate exactly these two gaps without weakening any statement.

Checked the new statements on the zero ring, zero scalar complexes, empty degree intervals,
empty schemes and empty covers. Bounds are allowed to depend on the original chart.
The dual comparison needs no scalar exactness; the descent comparison explicitly assumes
it and finite presentation. Continuous algebraic-closure coefficients remain the actual
continuous-function ring used by this item's unchanged statement.

## New nodes

`lem-sfb-ordinary-scalar-perfect-local-dual`: the original-chart dual-model comparison,
from the existing scalar-perfect dual computation, coefficient localization and exact
ringed restriction. Its degreewise isomorphisms and differential equation specify the
ordinary dual without a new scalar-dual construction.

`lem-sfb-ordinary-scalar-model-bounded-descent`: the finite-refinement and scalar-module
presentation bridge to the existing local-model cohomology-descent theorem. It handles
one arbitrary complex and is independent of duality. Both nodes cite the source proof's
perfect-factor argument and have complete proof descriptions and three Mathlib searches.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
