# Sheaf.Paper.FiniteCoefficientDirectImage

## Reason

Restore the quarantined, fully proved item and repair its current elaboration
failure without changing any definition or statement. Original compilation
reports unresolved constraints `u + 1 =?= max (u + 1) ?u` in the pro-etale
coefficient-map declarations. A minimal reproduction with
`trace.Meta.synthInstance` identifies `WeilConjectures.scalarReductionSiteSmall`
as the selected site-size instance. Its `max u (t + 1)` output leaves an
auxiliary universe unconstrained when the requested size is exactly `t + 1`.
Disabling it selects the ordinary site-size instance; restoring it at the end
preserves its availability for downstream elaboration.

No existing Lean declaration is edited. In particular all canonical maps,
public imports, proof bodies, hypotheses, conclusions and universes retain
their archived text. No target meaning changes; the independent reader checks this proof-context repair.

## Old

```lean
universe u v
```

The archive ended after its final namespace closure without an instance update.

## New

```lean
-- Fix the pro-etale site-size universe before elaborating scalar functors.
attribute [-instance] WeilConjectures.scalarReductionSiteSmall

universe u v
```

At the end of the restored file:

```lean
-- Keep the imported instance available to consumers of this module.
attribute [instance] WeilConjectures.scalarReductionSiteSmall
```

## Users

`tools/downstream.py ... --allow-missing --uses IsFiniteCoefficientDirectImageMap
finiteCoefficientDirectImageMap finiteCoefficientDirectImageMap_naturality
finiteCoefficientDirectImageMap_comp` finds zero live consumers, since the item
was quarantined. The following direct quarantined consumers are preserved;
their declarations keep exactly the same meaning, with no forced adaptations.
The node `lem-coef-finite-direct-image` and the containing unit route are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteCoefficientDirectImage | S2 | Restore original declarations with instance-search repair. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | Archived consumer; identical interface, no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Archived consumer; identical interface, no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Archived consumer; identical interface, no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Archived consumer; identical interface, no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Archived consumer; identical interface, no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Archived consumer; identical interface, no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Archived consumer; identical interface, no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Archived consumer; identical interface, no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Archived consumer; identical interface, no adaptation. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | Archived consumer; identical interface, no adaptation. |
| Sheaf.Paper.ProperOpenCoefficientMate | unclaimed | Archived consumer; identical interface, no adaptation. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | Archived consumer; identical interface, no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Archived consumer; identical interface, no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Archived consumer; identical interface, no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Archived consumer; identical interface, no adaptation. |

## Status

landed 20261021T182459-L-1196414 2026-10-21 (merge of deliver/S2/Sheaf.Paper.FiniteCoefficientDirectImage)
