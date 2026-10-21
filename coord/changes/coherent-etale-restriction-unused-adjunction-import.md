# Sheaf.AlgebraicGeometry.CoherentEtaleRestrictionIso

## Reason

The completed restriction-isomorphism proof uses the upstream `tensorSectionsComp`
and its pinned adjunctions directly. It does not use the separate
`TensorPullbackSectionAdjunction` interface. Remove that unused public import.
The theorem signatures and the selected isomorphism definition remain verbatim.

## Old

```lean
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
```

## New

The unused import is removed. All other existing public imports remain verbatim.
One private proof import, `Mathlib.CategoryTheory.Adjunction.CompositionIso`, is added.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.CoherentEtaleRestrictionIso --uses
coherentEtaleRestrictionIso` lists the following two downstream modules and the
item's own use in its definition. Neither downstream module uses declarations
owned by the removed import. Their original source files are compiled against the
modified item in the sandbox consumer check; neither needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CoherentEtaleRestrictionIso | R1 | Complete the normalized existence proof; remove an unused import. |
| Sheaf.AlgebraicGeometry.CoherentHigherImageClasses | X6 | Same definitions and statements; no source change. |
| Sheaf.AlgebraicGeometry.AffineCohomologyEtaleModuleRealization | unclaimed | Same definitions and statements; no source change. |

No target or definition changes meaning. The selected isomorphism retains exactly
its prescribed section formula, now with a complete existence-and-uniqueness proof.

## Status

landed 20261021T130125-L-2545050 2026-10-21 (merge of deliver/R1/Sheaf.AlgebraicGeometry.CoherentEtaleRestrictionIso)
