# ProfinitePointPullback proof elaboration scopes

## Reason

The stage-3 checker flags added `open`, `variable` and namespace commands as an
interface change and requests a change record. They support private proved helpers
and proof elaboration only. Every existing signature, definition, visibility and
public import is unchanged. No global instance or attribute is introduced. No
Challenge statement or definition changes and no target statement review is reopened.

## Old

```lean
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
```

All existing definitions and signatures remain verbatim.

## New

```lean
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
```

The module introduces `section ModuleMates` with local coefficient variables for
private helpers, then closes it. It temporarily closes `AlgebraicGeometry.ProEtale`
and opens `CategoryTheory.Functor` for private generic derived-category lemmas.
Their variables are confined to the closed sections `TransferUnits` and
`TransferAssociativity`. It then closes that namespace,
reopens `AlgebraicGeometry.ProEtale`, and reopens the `CategoryTheory.Obj` scope
for the remaining existing declarations. No declaration in these helper sections
is public. These commands change local name resolution and notation elaboration,
not the mathematical interface visible to importers.

## Users

The read-only downstream.py query reports thirteen transitive importers. Its
`--uses profinite_point_pullback` query lists only this item as a direct lexical
user. All transitive importers are recorded below. None requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProfinitePointPullback | B4 | private proof scopes only; existing interface unchanged |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | no change; proof scopes are local |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | no change; proof scopes are local |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | no change; proof scopes are local |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | no change; proof scopes are local |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | no change; proof scopes are local |
| Sheaf.Paper.CondensedPointBasisEvaluation | unclaimed | no change; proof scopes are local |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | C1 | no change; proof scopes are local |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | no change; proof scopes are local |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | no change; proof scopes are local |
| Sheaf.Paper.GeometricFieldProEtaleEvaluation | unclaimed | no change; proof scopes are local |
| TargetsCheck | unclaimed | no change; proof scopes are local |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | no change; proof scopes are local |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | A2 | no change; proof scopes are local |

## Status

landed 20261015T172915-L-557856 2026-10-15 (merge of deliver/B4/Sheaf.Paper.ProfinitePointPullback)
