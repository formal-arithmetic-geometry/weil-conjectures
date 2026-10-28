# Finite compact-support restriction comparison data and composition

## Reason

Proving sfCompactSupportRestriction_comp needs the already proved open-extension
cocycle and all-complex direct-image unit normalization. Both imported the item
for its comparison definitions. Extract those definitions into
Sheaf.Paper.SfCompactSupportRestrictionData, preserving their names, types, attributes,
and bodies. The item publicly reexports that module and keeps all original public
imports. Its original composition statement is unchanged and is proved by pasting
the open and direct-image cocycles.

The extraction also lets the normalization node cite the definitions rather than
the composition theorem, removing the otherwise circular DAG dependency.
This reference correction changes no mathematical hypothesis, map, or conclusion.
No adopted WeilConjectures module is changed.

A private realization-map construction is factored out of lift_module_iso to avoid
repeated kernel expansion of its linear natural transformation. This changes only
the proof of the same sectionwise-unique realization statement. These private
helpers are isolated in SfCoefficientRealizationAux to keep each file within
the compile-time limit; it exposes no new public declaration.

## Old

In ProEtaleOpenScalarRestrictionCoherence and CompactSupportScalarDirectNormalization:

```lean
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
```

CompactSupportCoefficientPresentation publicly imported the item transitively through
ProEtaleOpenScalarRestrictionCoherence. Its imports were:

```lean
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence
```

Normalization-node statement (verbatim):

Let $g:Z\to Y$ be a morphism of schemes and $\varphi:A\to B$ a map of finite commutative rings. For the ordinary direct-image functors $F=g_*^B$, $H=g_*^A$, scalar restrictions $x=\operatorname{Res}_\varphi^Z$, $y=\operatorname{Res}_\varphi^Y$, and the ordinary identity-on-sections comparison $c:F;y\cong x;H$ [lem-weil-proetale-direct-image-restriction-of-scalars], the inverse of the specified comparison sfDerivedImageRestriction [lem-sf-compact-support-restriction-of-scalars] is unitNormalized [lem-pur-derived-square-normalization-naturality]. Explicitly, for every cochain complex $I$, $Dy(\eta_F(I));\chi^{-1}_{QI};RH(x_{\mathrm{fac},I})=y_{\mathrm{fac},FI};Q(c_I);\eta_H(xI)$. No preservation of K-injectives by restriction is assumed.

## New

In ProEtaleOpenScalarRestrictionCoherence and CompactSupportScalarDirectNormalization:

```lean
public import Sheaf.Paper.SfCompactSupportRestrictionData
```

All their declaration signatures and proofs are unchanged. The open-coherence
module measured 86 seconds after this import change. Its four public comparison
and normalization definitions are extracted unchanged into
ProEtaleOpenScalarRestrictionData, and its proved private calculations into
ProEtaleOpenScalarRestrictionAux and
ProEtaleOpenScalarRestrictionRealizationAux. The original module publicly imports the
former and proof-imports all private helpers from the latter; it retains all
public coherence theorems. This splits the kernel and elaboration work without
changing a public definition body, attribute, or theorem signature. The existing
open-coherence node now records the new ownership and uses the definition node
def-sf-open-scalar-restriction-data. Its mathematical statement is unchanged. The presentation's existing public
API is preserved by explicitly importing the proved composition module:

```lean
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
```

The ten existing public declarations now reside in the data module and remain
publicly reexported by the item. Only the private proof of their existing
realization-isomorphism construction is factored through a private map and its
section equation. No public definition body or signature changes.

Normalization-node statement (verbatim):

Let $g:Z\to Y$ be a morphism of schemes and $\varphi:A\to B$ a map of finite commutative rings. For the ordinary direct-image functors $F=g_*^B$, $H=g_*^A$, scalar restrictions $x=\operatorname{Res}_\varphi^Z$, $y=\operatorname{Res}_\varphi^Y$, and the ordinary identity-on-sections comparison $c:F;y\cong x;H$ [lem-weil-proetale-direct-image-restriction-of-scalars], the inverse of the specified comparison sfDerivedImageRestriction [def-sf-compact-support-restriction-data] is unitNormalized [lem-pur-derived-square-normalization-naturality]. Explicitly, for every cochain complex $I$, $Dy(\eta_F(I));\chi^{-1}_{QI};RH(x_{\mathrm{fac},I})=y_{\mathrm{fac},FI};Q(c_I);\eta_H(xI)$. No preservation of K-injectives by restriction is assumed.

The five private-lemma consumers IntrinsicCompactSupportRestriction,
CompactSupportRestrictionIdentity, CompactSupportQuotientInputLaws,
FiniteOpenScalarRealizationTransport and FiniteOpenScalarSiteTransport were
unclaimed on the live claim table when adapted. They keep their original
`import all Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence` and
add the private auxiliary import owning the lemma they already used. Only
FiniteOpenScalarRealizationTransport needs ProEtaleOpenScalarRestrictionAux
(for forward_realization_mate); the other four need
ProEtaleOpenScalarRestrictionRealizationAux (for restriction_comp_apply,
coefficient_id_apply or fixed_normalized). No declaration or proof body changes.

## Users

The table includes the direct importers of the four changed interfaces and all
source consumers mentioning a moved public declaration. The only consumers of
sfCompactSupportRestriction_comp found by downstream.py --uses are
CompactSupportFiniteCoefficientCocycle and ProperFiniteNormalization; both retain
the same theorem through their existing imports.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SfCoefficientRealizationAux | P4 (new) | Extracted existing comparison data or proved private calculations; no new proof obligation. |
| Sheaf.Paper.SfCompactSupportRestrictionData | P4 (new) | Extracted existing comparison data or proved private calculations; no new proof obligation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionData | P4 (new) | Extracted existing comparison data or proved private calculations; no new proof obligation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionRealizationAux | P4 (new) | Extracted existing comparison data or proved private calculations; no new proof obligation. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionAux | P4 (new) | Extracted existing comparison data or proved private calculations; no new proof obligation. |
| Sheaf.AlgebraicGeometry.ProEtaleIdentityOpenScalarRestriction | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionCoherence | unclaimed | Extracted comparison data and private mate calculations; publicly reexports all original declarations with identical signatures and bodies. |
| Sheaf.Paper.CoefSupportOpenTensorModel | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.CompactSupportCoefficientPresentation | unclaimed | Updated import layering only; existing signatures and bodies stay identical. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.CompactSupportFiniteCoefficientCocycle | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.CompactSupportIntrinsicTensorComparison | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.CompactSupportNativeDirectTransition | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.CompactSupportNativeOpenTransition | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.CompactSupportNativeRealization | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.CompactSupportNativeSystemTransition | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.CompactSupportNormalizedRealization | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.CompactSupportOpenScalarRestriction | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.CompactSupportOrdinaryOpenTransition | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.CompactSupportQuotientCocycle | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.CompactSupportQuotientCocycleData | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.CompactSupportQuotientInputLaws | unclaimed | Add private import Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionRealizationAux for the same proved helper; all declarations and proofs unchanged. |
| Sheaf.Paper.CompactSupportQuotientRawOutputComposition | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.CompactSupportQuotientRawOutputIdentity | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.CompactSupportRealizedScalarTranspose | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.CompactSupportRealizedScalarTransposeProjection | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.CompactSupportReductionAdjoint | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.CompactSupportReductionTower | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.CompactSupportReductionTowerData | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.CompactSupportRestrictionIdentity | unclaimed | Add private import Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionRealizationAux for the same proved helper; all declarations and proofs unchanged. |
| Sheaf.Paper.CompactSupportScalarDirectNormalization | unclaimed | Updated import layering only; existing signatures and bodies stay identical. |
| Sheaf.Paper.CompactSupportScalarEvaluationSquare | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.EtaleOriginExtensionPullbackCube | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.EtaleOriginRestrictionPullbackCube | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.ExceptionalAdjointAdmissibility | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.ExceptionalFiniteScalarMatesData | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.FiniteCompactScalarConstructible | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.FiniteCompactSupportScalarComparison | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.FiniteCompactSupportScalarTransport | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.FiniteCompactSupportScalarTransportData | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.FiniteOpenScalarRealizationTransport | unclaimed | Add private import Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionAux for the same proved helper; all declarations and proofs unchanged. |
| Sheaf.Paper.FiniteOpenScalarSiteTransport | unclaimed | Add private import Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionRealizationAux for the same proved helper; all declarations and proofs unchanged. |
| Sheaf.Paper.FiniteOpenScalarTransport | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.FiniteProperScalarTransport | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.FiniteRealizationOrdinaryRestrictionCube | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.FiniteRealizationRestrictionCube | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.FiniteRealizationScalarMate | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.FiniteReductionExceptionalFiniteModel | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.IdentityCompactificationSystemMate | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.OpenScalarCounitSquare | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.ProperEtaleOriginScalarData | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.ProperFiniteNormalization | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.RecordedOpenScalarNormalization | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.RecordedProperScalarNormalization | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.RecordedRestrictionNormalization | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.SfCompactSupportRestrictionOfScalars | P4 | Composition hole proved; original public API reexported through the data module. |
| Sheaf.Paper.SfFiniteOpenCoefficientGenerators | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.SfFiniteOpenPresentation | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.SfIntegralCompactSupportTower | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.SfIntrinsicOpenUnitGenerators | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.SfSupportTransitionPresentation | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.SupportScalarProjectionNormalization | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.Paper.SystemOpenScalarEvaluation | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.Paper.SystemProperScalarEvaluation | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | Add private import Sheaf.AlgebraicGeometry.ProEtaleOpenScalarRestrictionRealizationAux for the same proved helper; all declarations and proofs unchanged. |
| Sheaf.SecSmoothPurity.ReductionExceptionalObjects | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.SixFunctors.ConstructibleReductionGood | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.SixFunctors.IntegralPullEvaluationQuotientSquare | H4 | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.SixFunctors.IntegralSystemDirectEvaluation | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Direct importer; same declarations, statements, and definition bodies via the new data module. |
| Sheaf.SixFunctors.OpenSupportStepBounds | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |
| Sheaf.SixFunctors.ProperSupportStepBounds | unclaimed | Named consumer; same declarations and definition bodies, no adaptation needed. |

## Status

landed 20261028T034905-L-3565737 2026-10-28 (merge of deliver/P4/Sheaf.Paper.SfCompactSupportRestrictionOfScalars)
