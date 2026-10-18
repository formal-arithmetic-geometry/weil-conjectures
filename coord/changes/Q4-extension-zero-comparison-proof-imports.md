# AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparison_coherence

## Reason

Prove the canonical comparison coherence directly from the existing comparison isomorphism,
restriction adjunctions and adjunction-square pasting. Remove unused statement-module reexports
and proof imports so that their unrelated obligations are not dependencies of this item.
No existing declaration type, visibility or definition body changes.

## Old

```lean
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
```

These exported legacy coherence lemmas, the site-comparison statements and the unrelated threefold etale-extension
coherence theorem. The last import also exported the composition, coefficient-category
and identity-comparison APIs needed to type this module.

## New

```lean
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
```

Keep ProEtaleSiteComparison as a proof-only import for the unit route identified
by the delivery base. Retain precisely the APIs used in existing public signatures and definition bodies.
Add proof-only imports for HeartGluing, AdjunctionSquareComposition and adjunction uniqueness.
All newly written helpers are private and proved. Target statements and their definitions
are unchanged.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
--uses openImmersionLowerShriekComparison_coherence proEtaleOpenExtensionComp` reports
zero downstream modules on the read-only snapshot (2026-10-18). There are therefore no
consumer adaptations to make or compile.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison | Q4 | Same public declarations; remove unused reexports; prove coherence. |

## Status

landed 20261018T062855-L-670922 2026-10-18 (merge of deliver/Q4/Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison)
