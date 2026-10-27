## What changed

Replaced the hole in `WeilConjectures.clopenIntegralCompletionRestriction` with the
strict-tower comparison, an additive comparison of the actual shifted Roos complexes,
and the universal property of `integralPullbackDescent`. The target signature and
its public import are preserved.

Added `Sheaf.Paper.ClopenPullbackQuotientTower`, proving
`WeilConjectures.clopenPullbackQuotientTower`. Its coefficient-adjunction argument
identifies normalized ordinary restriction with the actual ambient module pullback.
It assembles the existing clopen scalar quotient comparisons into a natural strict
tower isomorphism, checking transitions and naturality on sheafified pure tensors,
and composes with the already proved normalized ambient pullback tower model.
This module contains no `sorry`.

Profiling isolated the coefficient-adjunction argument and the strict tensor
coherence argument. They are proved in `ClopenOrdinaryPullbackComparison` and
`ClopenScalarQuotientTower`, respectively. Local definition presentations were
simplified and the generic ringed-site adjunction was factored before separating
these self-contained arguments, as permitted by the brief’s step 3a. The new
modules contain no holes.

The item’s added imports are private proof imports. Only the item, the three new support modules,
and their DAG records change. No shared definition or other existing module changes.
All four modules compile without errors or warnings using `lcompile.py --all`
with profiling removed and the normal acceptance limit. The listed service times
include artifact preparation, so acceptance is the compiler service’s return code,
which enforces the limit on the Lean process itself. Locally irreducible canonical
coefficient, completion and Roos data avoid unnecessary unfolding; no shared
definition is changed.

## Proved and sorry left

Closed one hole and added zero holes. The item’s single closed hole is:
`WeilConjectures.clopenIntegralCompletionRestriction`
(`lem-fix-clopen-integral-completion-restriction`).

Also proved `WeilConjectures.clopenOrdinaryPullbackComparison`,
`WeilConjectures.clopenScalarQuotientTower`, and
`WeilConjectures.clopenPullbackQuotientTower`
(`lem-sf-clopen-pullback-quotient-tower`). No holes remain in the delivered modules;
no holes are added or split off. The proof uses the existing
`WeilConjectures.sf_clopen_scalar_quotient_comparison`, whose separate module already
contains its own named hole. That existing obligation is unchanged.

## No longer needed

No original public import is removed. The revised proof does not use:

- `lem-sf-clopen-derived-compatibility` / `Sheaf.Paper.SfClopenDerivedCompatibility`:
  only its existing scalar quotient comparison is needed; completeness and residue
  Tor preservation are unnecessary for the comparison of functors on all inputs.
- `lem-cbc-exact-product-functor-strict-limit` /
  `Sheaf.Paper.ExactProductFunctorStrictLimit`: the proof works with the
  actual chain-level Roos construction and the additive comparison in
  `Sheaf.CategoryTheory.StrictRoosAdditiveComparison`.

These are removals from this node’s planned proof dependencies. No module is
withdrawn. `ExactProductFunctorStrictLimit` remains reachable through pre-existing
imports of `OpenCompletedRestrictionIdentification`; this delivery does not claim
that it is globally pruned.

The existing coefficient comparison, integral operation definitions, and normalized
operation descent remain needed. The new support node uses the normalized ambient
pullback tower as a generic scalar-association theorem; the unit route is preserved.
The private Roos helper uses the additive Roos theorem's proved construction and
naturality lemmas as generic category-theoretic tools.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original plan supplied the mathematical route,
but the existing `sf_clopen_derived_compatibility` interface alone did not identify
the particular finite pullback tower. `NormalizedIntegralPullbackTower.pullTowerModel`
provides that missing bridge once the coefficient-normalized ordinary restriction
is identified with ambient pullback. The required coefficient comparison uses no
invertibility of the prime on the scheme.

Ordinary restriction preserves products directly by precomposition and reflection
of limits; a decomposition with the complementary clopen is unnecessary for that
step. Empty clopens and the zero complex use the same constructions and formulas.

## New nodes

`lem-sf-clopen-pullback-quotient-tower` records the proved strict-tower part of step 1
of the item. Its conclusion is before products, Roos complexes and localization.
It introduces no unproved obligation. Its coefficient adjunction, tensor-generator
naturality and transition checks are implemented in the new module. No change
record is required because no existing statement or definition changes.

`lem-sf-clopen-ordinary-pullback-comparison` records the coefficient-adjunction
part, proving existence of a natural comparison on all ordinary modules, without
any clopen assumption. It is fully proved.

`lem-sf-clopen-scalar-quotient-tower` records strict naturality and transition
coherence of the already supplied scalar quotient comparisons. It is fully
proved, before any Roos or descent operation.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
