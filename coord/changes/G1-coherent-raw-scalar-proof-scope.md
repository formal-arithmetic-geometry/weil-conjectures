# coherentRawScalarRestriction proof scope

## Reason

Preflight conservatively flags changes to top-level proof-support commands. The
completed proof uses an additional universe `v` only in its private generic
conjugation helper and additional local irreducibility attributes. It uses the
default transparency-respecting elaborator settings in place of the old disabled
settings. These commands affect elaboration of this file. Its original public
import, theorem signature and visibility are unchanged. All new imports are private
proof imports. Importers inherit the same mathematical interface, and no target
meaning changes.

## Old

The original universe command is `universe u`. Its proof-support commands are:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] affineRealizationRawEquiv coherentEtaleMap
  tensorPullback tensorPullbackObj
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange Etale.RawRestrictedComparison.sheafifyInstance
  Etale.RawRestrictedComparison.weakSheafifyInstance
```

## New

The universe command is `universe u v`; `v` occurs only in a proved private helper.
The proof-support commands are:

```lean
set_option autoImplicit false
attribute [local irreducible] affineRealizationRawEquiv coherentEtaleMap
  tensorPullback tensorPullbackObj coherentEtaleRestrictionIso
  Etale.sheafHDerivedEquiv Etale.sheafHToDerived CategoryTheory.derivedExtEvaluation
  Etale.rawRestrictedCohomologyComparison
  Etale.rawAffineComplexPullback Etale.normalizationCohomologyRestriction
  Etale.upperStarComp Etale.upperStar Etale.cohomology Etale.rightDerivedGlobalSections
  Etale.normalizationRestrictedIso Etale.normalizationPresheafComplex
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange Etale.RawRestrictedComparison.sheafifyInstance
  Etale.RawRestrictedComparison.weakSheafifyInstance
```

The existing public theorem has its original signature and a complete proof.
New proved private helpers do not occur in public signatures or data definitions.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.CoherentRawScalarRestriction --uses
coherentRawScalarRestriction` reports the two declaration users below. Its 3,287
transitive importers inherit the identical theorem type. No consumer is adapted.
The consumer was already landed according to `coord/queue-states.tsv`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CoherentRawScalarRestriction | G1 | Completed proof; local proof support. |
| Sheaf.AlgebraicGeometry.CoherentHigherImageModuleAction | unclaimed (landed) | Same theorem type; no adaptation. |

## Status

landed 20261026T065714-L-3196579 2026-10-26 (merge of deliver/G1/Sheaf.AlgebraicGeometry.CoherentRawScalarRestriction)
