# supportInjectiveExactModels local elaboration controls

## Reason

The comparison proofs manipulate large sheaf functors and chosen kernels. Local
reducibility attributes keep these constructions folded until their explicit API
is applied. The delivery classifier records top-level attribute commands as an
interface change, even though these attributes are local to this module.

## Old

The module has no local reducibility declarations.

## New

```lean
attribute [local irreducible] upperStar lowerStar upperStarLowerStarAdjunction
  finiteClosedUpperShriek
attribute [local irreducible] openSectionIso Sheaf.ΓNatIsoSheafSections
attribute [local semireducible] lowerStar
attribute [local irreducible] supportSectionComponent
attribute [local irreducible] supportSectionIso
attribute [local irreducible] derivedSupportComparisonIso
```

These commands affect elaboration only within the file. No exported definition,
instance, attribute, signature or public import changes. All added declarations
are private proved helpers. The existing theorem statement is verbatim.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.SupportInjectiveExactModels` | S6 | Proof elaboration only. |

No current Lean module imports this item or mentions its theorem. Its unfinished
DAG parents remain unchanged and can use exactly the same theorem statement.
The local attributes do not affect those consumers when they import the module.

## Status

landed 20261024T020445-L-2605880 2026-10-24 (merge of deliver/S6/Sheaf.AlgebraicGeometry.SupportInjectiveExactModels)
