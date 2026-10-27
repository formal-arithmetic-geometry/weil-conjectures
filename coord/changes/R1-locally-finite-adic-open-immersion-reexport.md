# LocallyFiniteAdicConstructibleRealization public open-immersion API

## Reason

The landing recheck of returned head cfc8799cbae found that
`Sheaf.Paper.LocallyFiniteAdicCompactSupportData` no longer sees
`ProEtale.adicOpenImmersionLowerShriek` or its adjunction. They were previously
available through the broad public `WeilConjectures.WeilSheaf.LowerShriek` import.
Reexport their owning `Adic.OpenImmersion` module explicitly in the item file.
The change is confined to imports; no mathematical definition or statement changes.

## Old

On main:

```lean
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafForgetAb
```

The returned head removed the first line without a replacement.

## New

```lean
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafForgetAb
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
```

The unused private imports of `ContinuousRationalDerivedRealization` and
`RationalRealizationScalarCoherence`, already removed by the returned delivery,
remain removed. Public definitions and all existing signatures remain verbatim.
The invalid unlanded decomposition is discarded and the original theorem proof
obligation restored; its original DAG node is unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.LocallyFiniteAdicCompactSupportData | not adapted; see current claim | Existing declarations and definitions unchanged; narrower public import preserves the open-immersion API. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | not adapted; see current claim | Existing declarations and definitions unchanged; narrower public import preserves the open-immersion API. |
| Sheaf.Paper.NativeAdicRealizationData | not adapted; see current claim | Existing declarations and definitions unchanged; narrower public import preserves the open-immersion API. |
| Sheaf.Paper.NativeCoefficientInverseImage | not adapted; see current claim | Existing declarations and definitions unchanged; narrower public import preserves the open-immersion API. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | not adapted; see current claim | Existing declarations and definitions unchanged; narrower public import preserves the open-immersion API. |
| Sheaf.Paper.NativeWeilLocalizingBrownAdjoints | not adapted; see current claim | Existing declarations and definitions unchanged; narrower public import preserves the open-immersion API. |
| Sheaf.Paper.SfAdicCommonStageDescentEquivalence | not adapted; see current claim | Existing declarations and definitions unchanged; narrower public import preserves the open-immersion API. |

No consumer is edited or delivered. The previously failing direct importer is
compiled with the item, in import order, before delivery; deliver3.py also checks
the remaining related modules and records its results in the report.

## Status

landed 20261027T210207-L-1669725 2026-10-27 (merge of deliver/R1/Sheaf.Paper.LocallyFiniteAdicConstructibleRealization)
