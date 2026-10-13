# AlgebraicGeometry.Etale.objectSections_naturality (unused public import)

## Reason
The proof uses object evaluation, localization restriction, composition units and
terminal evaluation. It uses no strict-local injective source comparison. Remove
that unrelated public import. All existing theorem signatures and definitions
are unchanged; no target meaning changes or renewed target review is required.

## Old
```lean
public import Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceComparison
public import Sheaf.AlgebraicGeometry.EtaleObjectSections
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
```

## New
```lean
public import Sheaf.AlgebraicGeometry.EtaleObjectSections
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
```
Private proved helpers provide the restriction-unit, composition-unit and
terminal-evaluation calculations. The terminal helper is generalized to
restriction along every arrow into the terminal object; it does not redeclare
the private pointwise terminal-evaluation theorem in EtaleObjectSections. Their additional universe is used only in
those helpers; the existing theorem keeps exactly its original signature.

## Users
The only direct importer also publicly imports StrictLocalInjectiveSourceComparison
itself, so the removed export remains available to it and its downstream modules.
The downstream declaration-use search finds only SourceStageSectionsNaturality.
No adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SourceStageSectionsNaturality | unclaimed | Own public strict-local import preserves every exported declaration; original compiles against this delivery. |

## Status
landed 20261013T022434-L-3222848 2026-10-13 (merge of deliver/V4/Sheaf.AlgebraicGeometry.ObjectSectionsNaturality)
