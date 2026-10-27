# AlgebraicGeometry.Etale.proper_directImage_finiteness

## Reason

Restore the quarantined module assigned to A3 in coord/rework.tsv. The archive
contains a complete zero-hole proof, but compilation reproduces unknown-constant
errors at its four uses of a constructibility equivalence retired by D9. Use the
identically typed canonical source theorem and its private proof import.
The restored copy compiles cleanly in 33.8 seconds via lcompile.py.
The quarantine archive itself is unchanged.

## Old

Private proof import and theorem application name in the preserved archive:

```lean
import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
```

```lean
Scheme.isConstructibleEtaleModuleSheaf_iff
```

The module is absent from lean/ at the repair base; its source is preserved at
`quarantine/Sheaf/AlgebraicGeometry/EtaleProperDirectImageFiniteness.lean`.

## New

Restored the whole archived module to
`lean/Sheaf/AlgebraicGeometry/EtaleProperDirectImageFiniteness.lean`, with:

```lean
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
```

```lean
Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf
```

Only the private proof import and four theorem applications differ from the
archive. Every existing signature and public import stays verbatim. No definitions
change, no target statement or meaning changes, and no node attachment or
mathematical dependency changes. The node already points to the restored path and
describes this proof route; no node file needs changing.

## Users

The normal downstream tool cannot resolve the absent item. The table below is
computed from source imports in lean/Sheaf, lean/WeilConjectures and quarantine/Sheaf.
All 47 transitive consumers are quarantined. Direct importers are
Sheaf.Paper.OrgogozoGoodModification, Sheaf.Paper.PbcFiniteDirectImageCohomology,
Sheaf.Paper.ProperDirectImageFiniteness, and
Sheaf.TraceFormula.PsiProperSurjectiveConstructibility. Only the middle two call
the declaration directly. Their calls have the unchanged theorem signature.
No consumer is edited; their existing claims do not affect this restoration.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AmplificationProper | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.CompactFiberStalk | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.CompletedConstructiblePreservation | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.CompletedConstructibleReductionControl | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleCompleteBaseChange | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.DualBaseChange | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ExchangeFunctoriality | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteExtensionCompactSupportBaseChange | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteExtensionProperBaseChange | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.GeometricFiberFiniteExtension | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.GeometricFiberQbar | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.IdentificationCoefficientTransport | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportUniformRestriction | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.PbcConstructibleReductionDirectImage | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.PbcFiniteDirectImageCohomology | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.PreservationConstructible | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ProperDirectImageFiniteness | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.QbarCompactSupportBaseChange | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.QbarProperBaseChange | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Quarantined; signature and meaning unchanged; no adaptation. |

## Status

landed 20261023T102352-L-2884303 2026-10-23 (merge of deliver/A3/Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness)
