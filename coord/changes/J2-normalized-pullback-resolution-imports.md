# Resolution-comparison imports for the normalized pullback square

## Reason

Restore `Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare` from its current
quarantine archive. The listed rework error combines the duplicate Sheaf resolution
comparison with the adopted upstream comparison imported by resolution normalization.
The compiler rejects their shared declaration names before checking the theorem.

Use the upstream resolution-comparison extension consistently in the canonical
comparison and both of its proof-support modules. It reexports the adopted common
resolution construction and supplies the same cached instances and composition helper.
The original upstream declarations and all source-library files are preserved.

The restored module also requires a public import of ModuleCohomologyFMap: its
public theorem statement mentions that declaration. After the collision was fixed,
Lean explicitly diagnosed this second visibility error.

## Old

In CanonicalCoherentEtaleComparison:

```lean
public import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
```

In CoherentEtaleComparisonMorphismExists, CoherentEtaleEffacingSequence, and the
quarantined QcoherentNormalizedPullbackSquare:

```lean
import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
```

In QcoherentNormalizedPullbackSquare:

```lean
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
```

## New

In CanonicalCoherentEtaleComparison:

```lean
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturalityExtension
```

In CoherentEtaleComparisonMorphismExists, CoherentEtaleEffacingSequence, and the
restored QcoherentNormalizedPullbackSquare:

```lean
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturalityExtension
```

In QcoherentNormalizedPullbackSquare, beside its other public imports:

```lean
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
```

Every declaration signature, visibility, proof body, and definition body in these
four modules is unchanged. The imported common-resolution comparison still uses the
module-derived resolution, exact forgetting, acyclic abelian resolution comparison,
and terminal Ext source change. The upstream presentation additionally spells out
two identity natural isomorphisms, siteExtNatIso and siteHNatIso. These do not alter
the cohomology comparison or the meaning of downstream statements. The DAG attachment
of new-module-cohomology-ext-resolution-naturality now names the upstream extension,
so automatic proof-import regeneration does not reintroduce the duplicate module.

## Users

The standard downstream tool currently reports zero active downstream modules, since
these consumers were quarantined by the sync. The table also includes the complete
transitive consumer graph obtained by reading both lean/ and quarantine/, with lean/
winning when both contain a module. No quarantined module is withdrawn or discarded.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison | unclaimed | Import migrated; all declarations unchanged; compiled in the repair set. |
| Sheaf.AlgebraicGeometry.CoherentEtaleComparisonMorphismExists | unclaimed | Import migrated; all declarations unchanged; compiled in the repair set. |
| Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback | E6 | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.AlgebraicGeometry.CoherentEtaleEffacingSequence | unclaimed | Import migrated; all declarations unchanged; compiled in the repair set. |
| Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback | P4 | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.AlgebraicGeometry.CoherentPowerComparison | Q1 | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekFiniteTypeDenseOpen | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.AlgebraicGeometry.FiniteRingCompactSupportFiniteness | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison | J1 | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare | J2 | Assigned quarantined item restored; imports repaired; statement and original hole preserved. |
| Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.DeligneLaumon.FiniteCompactSupportFibreSupportBound | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.AmplificationProper | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.CompactFiberStalk | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.CompactSupportCondensedRealization | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.CompletedConstructiblePreservation | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.CompletedConstructibleReductionControl | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.ConstructibleCompleteBaseChange | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.DualBaseChange | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.ExchangeFunctoriality | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.FiniteExtensionCompactSupportBaseChange | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.FiniteExtensionProperBaseChange | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.GeometricFiberFiniteExtension | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.GeometricFiberQbar | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.IdentificationCoefficientTransport | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.IntegralCompactSupportUniformRestriction | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.OrientedProperImageConstructibility | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.PbcConstructibleReductionDirectImage | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.PbcFiniteDirectImageCohomology | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.PreservationConstructible | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.ProperDirectImageFiniteness | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.QbarCompactSupportBaseChange | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.QbarProperBaseChange | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Quarantined consumer; unchanged signatures and common-resolution meaning; no source adaptation in this packet. |

## Status

landed 20261020T150646-L-2557060 2026-10-20 (merge of deliver/J2/Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare)
