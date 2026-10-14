# exists_cechRefinement_pushforward_total

## Reason

The proof crosses two rings of global sections. Local elaboration attributes keep
tensor pullback irreducible and give the existing section-module instance priority.
They are local to this file and do not change any declaration or exported attribute.
The static delivery checker conservatively treats new attribute commands as an
interface change, so this record documents their scope. The original statements,
definitions and visibility are identical. No dependent module requires adaptation.

## Old

No local proof-elaboration attributes after `noncomputable section`.
The public definition and theorem signatures are the signatures in the repository,
unchanged in this delivery.

## New

```lean
attribute [local irreducible] tensorPullback tensorPullbackObj
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
```

The attributes are confined to this file. Declaration-scoped transparency and
heartbeat options affect elaboration of proofs only. These use the same approach
as the existing coefficient tuple calculations in CechCupPullbackCompat.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CechRefinementPushforwardTotal | E4 | Proves the unchanged theorem. |
| Sheaf.Paper.CechRefinementResolutionBeta | unclaimed | No exported change; no adaptation. |

The downstream scan found 179 transitive importers. The only downstream declaration
user of exists_cechRefinement_pushforward_total is CechRefinementResolutionBeta.
Local attributes and theorem-local options are not seen by any importer.

## Status

landed 20261014T061023-L-2464805 2026-10-14 (merge of deliver/E4/Sheaf.Paper.CechRefinementPushforwardTotal)
