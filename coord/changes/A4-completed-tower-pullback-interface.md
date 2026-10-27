# Completed tower pullback: earlier exact interface

Group A4; repair of J1 item Sheaf.Paper.CompletedTowerPullback; 2026-10-22.

## Reason

The completion proof needs the existing unit-compatible Koszul/quotient comparison
and strict reduction/pullback comparison. Their statements only need earlier
augmentation and exact constant/pullback constructions, but their original imports
pointed to the later completed-pullback comparison and would form import cycles.
Separate those earlier constructions, retaining their original public API through
public imports. No WeilConjectures file or target signature changes.

## Old

The augmentation declarations were in CompletedTowerPullback; the exact constant,
completion-unit and tower-pullback declarations were in CompletedPullback.
Four comparison modules publicly imported Sheaf.Paper.CompletedTowerPullback;
StratumCompletionUnitRestriction publicly imported Sheaf.Paper.CompletedPullback.
The stratum node cited the later completed-pullback node as a statement dependency
without spelling out the already specified completion-unit construction.

The relocated public signatures, verbatim (including anonymous instances), were:

From Sheaf.Paper.CompletedTowerPullback:

```lean
theorem completedReductionModuleUnit_exists (T : Scheme.{u}) : ∃! τ : completedTowerConstant d T ⟶ completedReductionModuleTowerFunctor T d, ∀ (M : pbcModules T (pbcAdicCompletion T d)) (n : ℕ) (U : T.ProEtᵒᵖ) (x : M.val.obj U), ((τ.app M).app (op n)).val.app U x = reductionTensorSection T (pbcAdicProjection T d n) M U 1 x

def completedReductionModuleUnit (T : Scheme.{u}) : completedTowerConstant d T ⟶ completedReductionModuleTowerFunctor T d

def completedReductionTowerCounit (T : Scheme.{u}) : DerivedCategory.Qh ⋙ completedReductionTower T d ⟶ completedReductionHomotopyFunctor T d

def HasCompletedReductionTowerUnitNormalization (T : Scheme.{u}) (τ : completedDerivedConstant d T ⟶ completedReductionTower T d) : Prop

theorem completedReductionTowerUnit_exists (T : Scheme.{u}) : ∃! τ : completedDerivedConstant d T ⟶ completedReductionTower T d, HasCompletedReductionTowerUnitNormalization d T τ

def completedReductionTowerUnit (T : Scheme.{u}) : completedDerivedConstant d T ⟶ completedReductionTower T d
```

From Sheaf.Paper.CompletedPullback:

```lean
abbrev AdicCoefficientDatum.constantTower (T : Scheme.{t}) : reductionModules T (d.completedRing T) ⥤ d.towers T

abbrev AdicCoefficientDatum.derivedConstantTower (T : Scheme.{t})

def AdicCoefficientDatum.constantRlimAdjunction (T : Scheme.{t}) : d.derivedConstantTower T ⊣ completedRlim T (d.completedRing T)

abbrev completedReductionAugmentation (T : Scheme.{t}) : d.derivedConstantTower T ⟶ completedReductionTower T d

def AdicCoefficientDatum.completionUnit (T : Scheme.{t}) (K : d.derived T) : K ⟶ (completedRlim T (d.completedRing T)).obj ((completedReductionTower T d).obj K)

def AdicCoefficientDatum.TowerComplete (T : Scheme.{t}) (K : d.derived T) : Prop

abbrev AdicCoefficientDatum.towerModulePull {U V : Scheme.{t}} (f : U ⟶ V) : d.towers V ⥤ d.towers U

theorem AdicCoefficientDatum.towerModulePull_exact {U V : Scheme.{t}} (f : U ⟶ V) : PreservesFiniteLimits (d.towerModulePull f) ∧ PreservesFiniteColimits (d.towerModulePull f)

instance AdicCoefficientDatum.towerModulePull_finiteLimits {U V : Scheme.{t}} (f : U ⟶ V) : PreservesFiniteLimits (d.towerModulePull f)

instance AdicCoefficientDatum.towerModulePull_finiteColimits {U V : Scheme.{t}} (f : U ⟶ V) : PreservesFiniteColimits (d.towerModulePull f)

instance AdicCoefficientDatum.towerModulePull_additive {U V : Scheme.{t}} (f : U ⟶ V) : (d.towerModulePull f).Additive

abbrev AdicCoefficientDatum.towerPull {U V : Scheme.{t}} (f : U ⟶ V)

def AdicCoefficientDatum.constantPullbackIso {U V : Scheme.{t}} (f : U ⟶ V) : d.constantTower V ⋙ d.towerModulePull f ≅ proEtaleRingModulePullback f (d.completedRing V) (d.completedRing U) (d.integralRingIso f) ⋙ d.constantTower U

def AdicCoefficientDatum.derivedConstantPullbackIso {U V : Scheme.{t}} (f : U ⟶ V) : d.derivedConstantTower V ⋙ d.towerPull f ≅ d.pull f ⋙ d.derivedConstantTower U
```

## New

Each signature above is unchanged, as are every relocated construction body and
instance attribute. The six augmentation declarations are now defined in
Sheaf.Paper.CompletedReductionUnit and publicly re-exported by CompletedTowerPullback.
The fourteen exact interface declarations are now defined in
Sheaf.Paper.CompletedPullbackInterface and publicly re-exported by CompletedPullback.
The latter retains towerComplete_iff_intrinsic, completedPull, ordinaryToCompleted,
and its original public imports. Private augmentation helpers move with the unit.

CompletedConstantCoefficientEquivalence, CompletedQuotientUnitNormalization,
CompletedConstantPresentationTransport and CompletedKoszulQuotientComparison replace
`public import Sheaf.Paper.CompletedTowerPullback` with
`public import Sheaf.Paper.CompletedReductionUnit`.
StratumCompletionUnitRestriction replaces
`public import Sheaf.Paper.CompletedPullback` with
`public import Sheaf.Paper.CompletedPullbackInterface`.
Their declarations and proofs are otherwise unchanged.

The stratum node now explicitly defines its existing quotient unit as the derived
constant/Rlim adjunction unit followed by Rlim of the normalized strict quotient
augmentation. The new definition nodes replace the circular coarse dependency.
All hypotheses, conclusions and Lean signatures remain unchanged; its three existing
DAG citers remain valid. The statement_change record preserves the original text
and dependencies. Its legacy `by` field format is required by node_fields.py;
this work and the present delivery are stage 3.

The item now proves its three original holes from the existing exact-derived API,
strict reduction comparison and Koszul comparison. No new holes or arbitrary witness
choices are introduced. All 51 original public signatures of the reorganized modules
were compared with the combined relocated source: none changed or disappeared.
The source-level public-import check found no consumer using a lost export.
The Lean overlay has no import cycle; the DAG overlay adds no cycle.

## Users

Every source-level consumer of the relocated declarations is listed below, together
with every delivered module. Unchanged consumers continue to see the same names,
signatures, attributes and constructions through their original public imports.
The forced adaptation of the G4-held stratum module changes only its circular import.
Both consumers named by the returned global build compile unchanged against
the restored current-base packet. All signatures and visibility stay identical. Holder names below have been refreshed from current claim records;
new modules belong to this A4 repair packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.AlgebraicGeometry.AbsoluteKunnethComparison | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.AlgebraicGeometry.ConstructibleComparisonModuleExact | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedFunctor | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.AlgebraicGeometry.OrdinaryKunnethMap | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsTwist | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.AdicPullbackPresentationTransport | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.AdicSmoothBaseChange | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.AdicStratumCompletionUnit | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompleteProetale | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompletedBaseChangeMap | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompletedConstantCoefficientEquivalence | unclaimed | Only public import changes to CompletedReductionUnit; declarations unchanged. |
| Sheaf.Paper.CompletedConstantPresentationTransport | unclaimed | Only public import changes to CompletedReductionUnit; declarations unchanged. |
| Sheaf.Paper.CompletedDirectImageLimits | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompletedExchangeCoherence | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompletedExchangeUnit | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompletedFiniteExchangeCoordinates | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompletedIntegralPrincipalUnitCriterion | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.CompletedKoszulConstantTransport | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.CompletedKoszulQuotientComparison | unclaimed | Only public import changes to CompletedReductionUnit; declarations unchanged. |
| Sheaf.Paper.CompletedMapReduction | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompletedOpenExchangeTransport | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompletedProjectionCoherence | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompletedPullback | unclaimed | Relocated exact interface publicly re-exported; remaining declarations unchanged. |
| Sheaf.Paper.CompletedPullbackAdjunction | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.CompletedPullbackInterface | A4 | New earlier module containing existing declarations unchanged. |
| Sheaf.Paper.CompletedPullbackReduction | E4 | Original current source compiled unchanged against the restored packet in 39.8 seconds; no edit. |
| Sheaf.Paper.CompletedPullbackReflection | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompletedPullbackUnitTower | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompletedQuotientUnitNormalization | unclaimed | Only public import changes to CompletedReductionUnit; declarations unchanged. |
| Sheaf.Paper.CompletedReductionPullbackSquare | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompletedReductionSquare | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompletedReductionUnit | A4 | New earlier module containing existing declarations unchanged. |
| Sheaf.Paper.CompletedScalarUnitAdjunction | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.CompletedTensorUnitInsertion | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.CompletedTowerCompatibility | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompletedTowerCorners | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.CompletedTowerPullback | A4 | Own item: augmentation publicly re-exported; three proof holes closed. |
| Sheaf.Paper.CompletionMateComparison | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.CompletionUnitFiniteProjection | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.ConstantCompletionEquivalence | C1 | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.ConstantCompletionUnitNormalization | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.ConstantDerivedLimitResolutionUnit | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.ConstructibleCompleteBaseChange | unclaimed | No edit; towerPull retains its signature and construction through the original public re-exports. |
| Sheaf.Paper.ExchangeFunctoriality | unclaimed | No edit; TowerComplete retains its definition and meaning through the original public re-exports. |
| Sheaf.Paper.ExternalEvaluationTransposeNatural | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.ExternalRHomConePairingDefs | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.FiniteExtensionCompactSupportBaseChange | unclaimed | No edit; TowerComplete retains its definition and meaning through the original public re-exports. |
| Sheaf.Paper.FiniteExtensionProperBaseChange | unclaimed | No edit; TowerComplete retains its definition and meaning through the original public re-exports. |
| Sheaf.Paper.FinitePullbackStrictTowerComparison | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.FiniteQuotientOrdinaryComparison | unclaimed | No edit; completedReductionModuleUnit and its normalization theorem remain publicly re-exported with unchanged bodies and signatures. |
| Sheaf.Paper.FiniteQuotientTransitionCompatibility | unclaimed | No edit; completedReductionTowerCounit remains publicly re-exported with unchanged body and signature. |
| Sheaf.Paper.FourArrows | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.IntegralAmbientCoefficientPresentation | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.IntegralAmbientOperationModels | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.IntegralAmbientTowerComparison | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.IntegralCompletedTowerPullbackUniverses | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.IntegralDerivedOperationsOnSlices | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.IntegralLineTensorComparison | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.IntegralLineTensorComparisonDefinitions | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.IntegralLineTensorComparisonIso | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.NormalizedCompletedOperationModels | unclaimed | No edit; completionUnit API unchanged through the original public re-exports; the local IntegralOnSlice.completionUnit occurrence is distinct. |
| Sheaf.Paper.NormalizedFiniteComparisonExistence | unclaimed | No edit; completedReductionTowerCounit retains its signature, body and visibility through the original public re-exports. |
| Sheaf.Paper.OpenRestrictionCompleteness | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.PbcActualStrictPullback | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.PbcIntrinsicTowerComplete | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.PerfectQuotientExchangeNormalization | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | No edit; towerPull API unchanged through original public re-exports. |
| Sheaf.Paper.ProEtaleEtaleFiniteModels | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.PulledReductionComparisonData | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.PurLisseMorphismRigidity | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.PurityConventions | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.QuotientCornerFrobeniusStructures | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.RationalSliceCompletedEvaluation | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.RationalThickEvaluation | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.ReductionPullFiniteEvaluation | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.RestrictionLimitProjectionUnit | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.RingedOpenStrictReduction | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.RoosIntrinsicCompletenessEquivalence | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.SbcCompletedOperations | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.SfCompletedPullbackMateFactorization | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.SfConstructibleCanonicalCompleteness | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.SfExactPullbackCounitNormalization | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.SfImmersionCompletedPullbackComparison | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.SfOpenReductionAdjunctionTransport | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.StratumCompletionUnitRestriction | G4 | Only public import changes to CompletedPullbackInterface; declarations unchanged. |
| Sheaf.Paper.StrictQuotientDiagonalNormalization | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.StrictQuotientOrdinaryFlatPresentation | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.StrictQuotientPullbackComputation | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.StrictQuotientScalarBalancingData | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.StrictQuotientScalarDirectIsomorphisms | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.StrictScalarCompletionUnit | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.StrictScalarOrdinaryAdjunction | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |
| Sheaf.Paper.StrictTowerExchangeMateNormalization | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.Paper.WeilTensorProduct | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | No edit; same declaration API re-exported by original modules. |
| Sheaf.SixFunctors.OpenRoosUnitAdjunction | unclaimed | No edit; same declaration API re-exported by original modules. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompletedExchange | unclaimed | No edit; textual final-name match included for completeness; relocated APIs retain their signatures, bodies and public re-exports. |

The repair of returned head 44fa21fc83f adds NormalizedCompletedOperationModels
to this consumer inventory. Its IntegralOnSlice.completionUnit occurrence names
a distinct declaration with the same final name component. A fresh downstream
scan also adds ProEtaleCompositionTowerNormalization, which uses towerPull through
the unchanged public re-exports. Neither consumer needs adaptation.

The repair of returned head 72c2aa25d00 adds NormalizedFiniteComparisonExistence.
It marks completedReductionTowerCounit locally irreducible and uses it in the
finite-reduction counit comparison. The declaration's signature, body and visibility
are retained through the original public re-exports, so no consumer edit is needed.
The delivery is regenerated on current sheaf-dag by deliver3.py.

A fresh source-level downstream scan also identifies FiniteQuotientOrdinaryComparison
and FiniteQuotientTransitionCompatibility. They respectively use the normalized
module quotient unit and the derived reduction counit. Both retain access through
their original imports, with unchanged construction bodies and signatures.

The repair of returned head 3303661f6cd adds the four users reported by the
landing gate: ConstructibleCompleteBaseChange uses towerPull; ExchangeFunctoriality,
FiniteExtensionCompactSupportBaseChange and FiniteExtensionProperBaseChange use
TowerComplete. All four modules are currently unclaimed. The relocated declarations
keep their signatures, definition bodies and public visibility, so these uses retain
exactly the same types and meaning and need no source adaptation. The packet is
regenerated on current sheaf-dag by deliver3.py, which fetches the base itself.

The refreshed whole-library scan finds 110 textual consumer modules for the twenty
relocated names, all inventoried above. This deliberately includes final-name
matches for unrelated declarations (for example other namespaces' completionUnit),
so these matches do not assert semantic dependence. No matched file needs editing:
the actual relocated declarations retain the same signatures, bodies and public
re-exports. Holder entries are refreshed from the current claim records.

## Status

landed 20261022T113806-L-249289 2026-10-22 (merge of deliver/A4/Sheaf.Paper.CompletedTowerPullback)

Recovered from the returned landing recorded in
coord/repair-notes/Sheaf.Paper.CompletedTowerPullback.json. All nine original
packet modules compile on the current base on this repair retry, including the
item in 50.2 seconds, without warnings and under the unchanged 60-second limit.
The source-level scan of twenty relocated declaration names found 110 textual
consumer modules, all present in the inventory above. No upstream source-library
file or target signature is changed.

The return named two failing consumers. CompletedTowerDirectImage's unmodified
current source compiles against the recovered packet (35.5 seconds), so that file
needs no edit. CompletedPullbackReduction's unmodified current source also compiles against
the restored packet (39.8 seconds), including its existing final rfl. Removing
that tactic on the current base leaves an unsolved definitional equality.
Therefore neither consumer is adapted in this packet. An initial original
compile reached the unchanged 60-second limit; the completed retry is the
reported verification. The historical batch had several returned suspects, so
this run claims current compatibility, not a reproduction of that batch state.

For the G4-held StratumCompletionUnitRestriction, retaining its original public
import of CompletedPullback closes this source cycle:
CompletedTowerPullback -> StratumCompletionUnitRestriction -> CompletedPullback
-> CompletedTowerPullback. lcompile.py --all reports the cycle before compiling,
and import_direction.py confirms that the unmodified shared graph rejects the
new proof import. Replace only that public import with CompletedPullbackInterface;
all its declaration signatures, bodies and visibility are identical. A single-file
compile of the original can load the old graph, but it does not validate the
cyclic source packet; the repaired full packet is the required check.
