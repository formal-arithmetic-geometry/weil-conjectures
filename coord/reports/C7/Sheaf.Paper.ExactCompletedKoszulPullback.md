## What changed

Replaced the proof of
`CategoryTheory.ConstantCompletion.exactCompletedKoszulPullback` without changing its
signature or public imports. Added proof-only imports of the completed-pullback and
normalized strict-Roos machinery, the existing flat-scalar comparison module for its
proved generic unit-naturality helpers, and the new finite tower comparison module.

The proof establishes exactness and countable-product preservation of the actual module
pullback, identifies its specified left-derived functor with the termwise derived functor,
and uses `exactProductFunctorStrictLimit`. It extends the normalized Roos inclusion
identity from K-injective towers to arbitrary complexes and transports it from limits of
complexes to degreewise limits. The strict tensor comparison descends through localization;
the product projection formula proves compatibility with the ordinary limit augmentation.
The existing proved generic unit-naturality helpers are reused rather than duplicated.
Naturality, the given tensor factorization and the derived-limit comparison then prove the
actual completion-unit equation, first on localized complexes and then on all objects.

Added `Sheaf.Paper.StrictCompletedKoszulTowerPullback`, the finite tensor calculation from
step 2 of the original node. This statement has no countable-product, inverse-limit or
derived-category data. Its sole remaining proof is documented in coordinates, including
transitions and augmentation. Updated the parent proof and dependency list to match Lean.
No existing public definition or statement was changed; no consumer adaptation is needed.
Local irreducibility annotations keep the chosen localizations, completed coefficient limits,
pullback comparison and unit representatives from unfolding in the Koszul transport and
final naturality calculations; these annotations do not change the definitions or any importer’s context.
Private proved instances cache the pointwise limits of complexes. The tower comparison
uses definitional associativity of functor composition to avoid redundant associators.
The strict tensor isomorphism descends using Mathlib’s fully faithful precomposition
with localization, retaining the component equation without expanding lifting structures.

Validation: the required server `lcompile.py --all` run passed with no warnings:
`StrictCompletedKoszulTowerPullback` in 3.2 seconds and the item module in 48.6 seconds.
The original theorem signature and public imports are identical. The final proof selects
its intermediate comparisons without nested case splits over the dependent category data.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.ConstantCompletion.exactCompletedKoszulPullback`
(node `lem-sfb-exact-completed-koszul-pullback`): its proof now contains no `sorry`.

Added one hole:
`CategoryTheory.ConstantCompletion.strictCompletedKoszulTowerPullback`
(node `lem-sfb-strict-completed-koszul-tower-pullback`). Its proof is exactly `by sorry`
in its own new module, with source and complete proof in words.

This is a decomposition: one upper hole closed and one strictly smaller finite-tower hole
added, for net zero holes closed among the declarations changed in this packet. All private
helpers are proved; no holes occur in private declarations or definitions. The substantial derived-limit, localization and unit
transport argument is complete, conditional on the finite augmented tower comparison.

Edge cases of the new statement: for zero generators the sole summand is the original
complex; zero rings, zero or repeated scalars and unit scalars satisfy the same component
formulas. The statement concerns arbitrary unbounded complexes but only a finite tensor
at each tower index, so there is no boundedness or interchange-of-infinite-sums assumption.

## No longer needed

No original imports were removed. Removed redundant proof imports of
`Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory`,
`Mathlib.Algebra.Homology.BifunctorShift`, and
`WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit`: their needed declarations
are already available through the actual dependency imports. No module or node is
withdrawn or globally pruned.
The parent no longer calls
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` directly: the finite tensor calculation
is now isolated in the new child, which retains that dependency. This is not global pruning.
The other original declared dependencies remain used. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The public completed-pullback adjunction specializes to
constant Noetherian coefficients, whereas this item permits arbitrary completed
coefficients. Its existing generic private module-adjunction and exactness proofs apply
without that restriction; the proof imports those through `import all`, without changing
their source module.

The strict-limit theorem uses limits in the category of complexes and normalizes its
comparison on K-injective towers. The supplied Koszul presentations use degreewise limits
and arbitrary complexes. These are compatible but require the explicit normalization and
ordinary-limit isomorphism arguments supplied here. No statement change is required.

## New nodes

`lem-sfb-strict-completed-koszul-tower-pullback` is the finite augmented strict Koszul tensor
calculation in original step 2, placed in
`lean/Sheaf/Paper/StrictCompletedKoszulTowerPullback.lean`. Its self-contained statement,
source, coordinate proof, edge cases, Mathlib searches, Lean attachment and blueprint
ancestry are in its node file. It is strictly simpler than the parent because it contains
no product exactness, inverse limits, derived presentations or completion units.

No change records: all existing signatures, public imports and definitions are preserved.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
