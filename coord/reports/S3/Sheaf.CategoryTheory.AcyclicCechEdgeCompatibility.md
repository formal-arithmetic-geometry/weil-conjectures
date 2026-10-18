## What changed

Proved the three declarations of `Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility`
without changing their signatures, definitions, or public imports. The construction
uses explicit restriction and coefficient augmentations. First-quadrant augmentation
proves their required quasi-isomorphisms; commuting total-complex squares give
coefficient naturality, site change, and forgetting scalars.

Used `module_abelian_evaluation_comparison` for the existing natural scalar-forgetting
isomorphism, its degree-zero normalization, and its all-resolution formula. All new
helpers are private and proved. Locally marking the resolution bicomplex and its
constructed augmentations irreducible keeps their data out of instance search;
these attributes are scoped to the comparison proofs and do not affect importers.
Updated the existing node's proof and proof dependencies to this route. No other Lean
module is changed. New proof imports supply total-complex symmetry,
the constructive generalized resolution lift, and the existing scalar comparison.
The static interface check also required the scope-only change record
`coord/changes/acyclic-cech-edge-local-proof-scopes.md`; it lists all ten downstream
modules and explains why the private section variables and local attributes do not
change their public interface. No consumer adaptation is needed.
The comparison statements retain their original proof-binder names; their local
unused-variable linter exception is limited to those existing declarations.

## Proved and sorry left

Closed the three existing holes:

- `CategoryTheory.exists_acyclicCechEdge`.
- `CategoryTheory.acyclicCechEdge_siteChange`.
- `CategoryTheory.acyclicCechEdge_forgetModules`.

All belong to `lem-weil-pbc-acyclic-cech-edge-compatibility`.
No holes added, no split-offs, and no `sorry` remains in the delivered module.
The complete three-proof version compiled in 45.6 seconds. After removing the
temporary profiling settings, the required delivery dry run compiled the final
module and passed preflight (review class CODEX).
Dependencies retain their existing proof status; in particular the scalar comparison
is an existing declared dependency, not a new assertion of this delivery.

## No longer needed

Removed these direct proof dependencies from the node:

- `lem-weil-pbc-lift-along-injective-quasi-iso`.
- `lem-weil-pbc-ring-sheaves-grothendieck`.
- `lem-sc-injective-module-abelian-acyclic-zariski`.
- `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`.
- `lem-weil-pbc-site-cohomology-pullback`.
- `lemma-weil-pbc-leray-acyclicity`.

Chosen-resolution uniqueness and the derived-functor map formula replace a separate
total homotopy argument. The site-change statement is proved directly for every strict
resolution lift, without calling a separate site-cohomology pullback construction.
The existing scalar comparison supplies the acyclic-resolution identification, so this
module does not separately invoke underlying injective-module evaluation acyclicity or
the Leray acyclic-resolution theorem. Those results may still be needed by the existing
scalar comparison; this pruning concerns direct dependencies of this node.

The constructive `descOfQuasiIso` also avoids the model-category lifting theorem.
The upstream equal-universe `SheafOfModules.isGrothendieckAbelian` theorem supplies
the module-category instance, so the separate universe-enlargement node is unused.

Removed these imports (some are duplicate re-exports or still supplied by statement
imports):

- `Mathlib.Algebra.Homology.ModelCategory.Injective`.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`.
- `Mathlib.CategoryTheory.Abelian.Injective.Resolution`.
- `Mathlib.CategoryTheory.Abelian.RightDerived`.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `Sheaf.CategoryTheory.DoubleComplexTotal`.
- `Sheaf.CategoryTheory.SiteCechComplex`.
- `Sheaf.CategoryTheory.SiteCohomologyPullback`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`.
- `Sheaf.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic`.
- `WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`.
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`.
- `WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor`.
- `WeilConjectures.CategoryTheory.SiteCechComplex`.
- `WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic`.

The obsolete `tool_uses` entries for
`lem-sc-injective-module-abelian-acyclic-zariski` and
`lemma-weil-pbc-leray-acyclicity`, and `lem-weil-pbc-ring-sheaves-grothendieck` were removed; the remaining entries retain their order.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The planned explicit total homotopy and
separate construction of the scalar cohomology comparison were unnecessary: existing
resolution naturality and the existing scalar comparison provide a shorter route.
Forgetting compatibility obtains the module edge's invertibility from the abelian edge
and the scalar isomorphism; a separate proof of quasi-isomorphism of the module beta is
not needed. The unit's statements and realized proof steps are preserved.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
