# ContinuousCoefficientUniverse imports

## Reason

The sheaf well-definedness proofs use only continuous maps and profinite-site
infrastructure. MorphismDefs brings the derived base-change framework into
scope but no declaration from it is used. Replace that re-export by the direct
Mathlib profinite import. EffectiveEpi must be public: Profinite and its
Precoherent instance occur in the existing public coherent-topology signatures.
TopComparison is used only in proofs and remains private. No existing
signature or definition changes; no target statement needs semantic review.

## Old

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
```

## New

```lean
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap

import Mathlib.Condensed.TopComparison
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`
reports exactly one downstream module:

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Already imports MorphismDefs explicitly; original source compiles unchanged against the sandbox overlay. Its statements and definitions retain their meaning. |

No adapted module is delivered. The node lean note and module description now
reflect reuse of the existing framework by users rather than this re-export.

## Status

landed 20261015T154151-L-158405 2026-10-15 (merge of deliver/B2/Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse)
