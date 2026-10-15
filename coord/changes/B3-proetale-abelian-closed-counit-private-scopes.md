# AlgebraicGeometry.ProEtale.abelian_closed_counit: private proof scopes

## Reason

The stage-3 static interface detector treats added universe, open, section-variable and
local-attribute commands as changes to what other modules see. Record these commands
explicitly for review. They support private proof helpers; the existing public imports and
public theorem statement are unchanged. The two continuity lemmas are private and are
registered as instances only locally in `section Localization`, so they add no exported
instance registration. No target statement, existing definition, or existing theorem
signature changes.

## Old

The module had only these proof scopes:

```lean
universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale
```

Its public theorem signature was:

```lean
theorem abelian_closed_counit {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    IsIso (upperStarLowerStarAdjunction Ab.{u + 1} i).counit
```

## New

The proof additionally uses the coefficient-category universe and categorical notation:

```lean
universe u u'

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite
```

Inside the original namespace it opens `Scheme MorphismProperty`. The added `Localization`
section binds the scheme-square and sheaf-category parameters of
private helpers. The only new instance registration is local:

```lean
attribute [local instance] counitPullbackMapContinuous counitMapPullbackContinuous
```

The public theorem signature remains verbatim:

```lean
theorem abelian_closed_counit {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    IsIso (upperStarLowerStarAdjunction Ab.{u + 1} i).counit
```

All new declarations are private. The helper definitions construct actual maps and have
no postponed data. Users therefore need no source adaptation.

## Users

`tools/downstream.py` lists the following 18 transitive users. Its declaration-name scan
finds only `Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport` using
`AlgebraicGeometry.ProEtale.abelian_closed_counit` directly. Holders are the claim snapshots
at preparation time; none of these modules is edited in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport | unclaimed | Uses the unchanged counit theorem; no adaptation. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Imports the unchanged interface transitively; no adaptation. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Imports the unchanged interface transitively; no adaptation. |
| Sheaf.Paper.CondensedConstructibleOneStep | J1 | Imports the unchanged interface transitively; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Imports the unchanged interface transitively; no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | G2 | Imports the unchanged interface transitively; no adaptation. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | H3 | Imports the unchanged interface transitively; no adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Imports the unchanged interface transitively; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Imports the unchanged interface transitively; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Imports the unchanged interface transitively; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | Imports the unchanged interface transitively; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Imports the unchanged interface transitively; no adaptation. |
| Sheaf.Paper.CondensedStratumModelAssembly | XR1b27919aec52b018 | Imports the unchanged interface transitively; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Imports the unchanged interface transitively; no adaptation. |
| TargetsCheck | unclaimed | Imports the unchanged interface transitively; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Imports the unchanged interface transitively; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Imports the unchanged interface transitively; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Imports the unchanged interface transitively; no adaptation. |

## Status

landed 20261015T221610-L-2628303 2026-10-15 (merge of deliver/B3/Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedCounit)
