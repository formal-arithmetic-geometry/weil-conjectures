# FrobeniusPointTransport private proof context

## Reason

The proofs compare scalar actions through nested section and inverse-image
functors. Disable transparency checks for types in this file, matching the
coefficient comparison modules. Treat the Frobenius isomorphism and its site
arrow as locally irreducible during elaboration. Temporarily remove broad
sheafification instances only around each newly proved declaration; the `in`
scope restores them after that declaration. No instance registration is changed
for importers. All mathematical definitions, target statements and public
imports retain their meanings.

## Old

```lean
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
```

## New

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [local irreducible] frobeniusPointIso frobeniusPointRestriction
```

Each proof declaration is additionally scoped by:

```lean
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
```

## Users

The downstream inventory contains the following twenty-five modules. None needs an
adaptation because these elaboration settings do not change exported signatures
or data.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.FrobeniusPointTransport | Z9 | Proved here. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.FourierArtinSchreierProperties | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTrace | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality | H1 | Identical public interface; no adaptation. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | Identical public interface; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | M5 | Identical public interface; no adaptation. |
| Sheaf.TraceFormula.PointTransportComposition | D4 | Identical public interface; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.LisseFieldNormalization | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.LissePointNormalization | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.LisseRationalRealization | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Identical public interface; no adaptation. |
| Sheaf.Paper.RealWeights | unclaimed | Identical public interface; no adaptation. |

## Status

landed 20261021T194614-L-1782105 2026-10-21 (merge of deliver/Z9/Sheaf.SixFunctors.FrobeniusPointTransport)
