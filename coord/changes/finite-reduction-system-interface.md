# AlgebraicGeometry.FiniteReduction: interface extraction and equivalent definition bodies

## Reason

The theorem needs independent results on scalar extension, its universal derived functor,
constructibility, and coherence. Extract its concrete interface into
`Sheaf.Paper.FiniteReductionSystem`, publicly imported by the original module, so these
proofs can import it without a cycle. All 14 moved declarations keep their names,
visibility and verbatim signatures. Their data bodies remain unchanged except for the
explicit proof argument in `ordinaryAssociator` below. No adopted source file changes.

The old implicit quotient-composition proof made elaboration unfold large sheafification
terms and exceed the per-file limit. The new proof gives the same ring-hom equality
explicitly. Proof irrelevance makes its use in the ordinary associator identical.
`System.originComparison` now displays the same composite isomorphism as a structure;
its hom and inverse are exactly those of the original transitive composite. Neither
change chooses different maps or changes any hypothesis or conclusion.

The independent reader should verify this semantic identity, including definitions
appearing in target dependencies. This record reopens that check for any affected target;
no text in `Challenge.lean`, target signature, or definition's mathematical meaning changes.

## Old

Original location: `lean/Sheaf/Paper/FiniteReductionConstructibility.lean`.
The two definition bodies whose syntax changes are reproduced verbatim:

```lean
def ordinaryAssociator {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    (l : ℕ) {r m n : ℕ} (hmr : m ≤ r) (hnm : n ≤ m) :
    extend J (quotient.{u} l hmr) ⋙ extend J (quotient l hnm) ≅
      extend J (quotient l (hnm.trans hmr)) :=
  Adjunction.leftAdjointUniq
    (((extendAdjunction J (quotient l hmr)).comp
      (extendAdjunction J (quotient l hnm))).ofNatIsoRight
        (Sheaf.restrictScalarsCompIso J (quotient l hmr) (quotient l hnm)
          (quotient l (hnm.trans hmr))
          (RingHom.ext (fun x ↦
            congrArg (fun y : ZMod (l ^ n) ↦ (⟨⟨y⟩⟩ : Coeff.{u} l n))
              (DFunLike.congr_fun
                (Subsingleton.elim
                  (ZMod.castHom (pow_dvd_pow l (hnm.trans hmr)) (ZMod (l ^ n)))
                  ((ZMod.castHom (pow_dvd_pow l hnm) (ZMod (l ^ n))).comp
                    (ZMod.castHom (pow_dvd_pow l hmr) (ZMod (l ^ m))))) x.down.down)))))
    (extendAdjunction J (quotient l (hnm.trans hmr)))
```

```lean
def System.originComparison {T : Scheme.{u}} {l : ℕ} (S : System T l)
    {r m : ℕ} (h : m ≤ r)
    {K₀ : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r)))}
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Coeff.{u} l r)))}
    (e : (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l r)) T).mapDerivedCategory.obj K₀ ≅ K) :
    (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l m)) T).mapDerivedCategory.obj
      ((S.etale r m h).functor.obj K₀) ≅ (S.proetale r m h).functor.obj K :=
  (S.comparison r m h).app K₀ ≪≫ (S.proetale r m h).functor.mapIso e
```

The remaining moved declarations are `Ring`, `Coeff`, `quotient`, `extend`,
`extendAdjunction`, `extend_additive`, `DerivedExtension`, `ordinaryComparison`,
`ordinaryComparisonComplex`, `System`, `System.CoherentAt`, `ringFinite`, and `realize`.
Their signatures and data are preserved in the extracted module (docstrings only acquire
their owning node identifiers).

## New

The original module publicly re-exports the extracted interface:

```lean
public import Sheaf.Paper.FiniteReductionSystem
```

New location of the ordinary associator: `lean/Sheaf/Paper/FiniteReductionSystem.lean`.

```lean
def ordinaryAssociator {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
    (l : ℕ) {r m n : ℕ} (hmr : m ≤ r) (hnm : n ≤ m) :
    extend J (quotient.{u} l hmr) ⋙ extend J (quotient l hnm) ≅
      extend J (quotient l (hnm.trans hmr)) :=
```

`System.originComparison` remains in the original module:

```lean
def System.originComparison {T : Scheme.{u}} {l : ℕ} (S : System T l)
    {r m : ℕ} (h : m ≤ r)
    {K₀ : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (Coeff.{u} l r)))}
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Coeff.{u} l r)))}
    (e : (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l r)) T).mapDerivedCategory.obj K₀ ≅ K) :
    (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Coeff.{u} l m)) T).mapDerivedCategory.obj
      ((S.etale r m h).functor.obj K₀) ≅ (S.proetale r m h).functor.obj K :=
```

## Users

The table is the union of the source-only `tools/downstream.py --uses` results for all
14 moved declarations and `System.originComparison`. The tool matches unqualified last
segments and deliberately over-approximates: for example the three finite-smooth files
have their own `Etale.FiniteSmoothPurity.ordinaryAssociator`, which is not the definition
changed here. The unchanged names and public re-export preserve visibility for every
listed module. The declaration reader confirms that every moved signature and the main
theorem signature are identical. No consumer statement becomes stronger or weaker. The sole direct importer,
`Sheaf.Paper.ExceptionalCoefficientComparison`, compiles unchanged against the full
updated overlay (26.7 seconds through lcompile); its temporary copy is not delivered.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.AdicSectionCanonicalModels` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekInterfaces` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.CoefficientTowerTransitionCompatibility` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.ExceptionalCoefficientComparison` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.FiniteProperLocalizing` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.FiniteReductionConstructibility` | {'who': 'R1', 't': 1792515537.0932937, 'since': '2026-10-20T16:58:57Z'} | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.FiniteSmoothCoefficientArrows` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.FiniteSmoothPurityMaps` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.FiniteSmoothQuotientCoherence` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.FiniteSmoothTwoLevelReduction` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.ProjectionTensorCoefficientComparison` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.TensorAdjunctionExchange` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.TowerClassReduction` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.VectorBundlePurity` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | {'who': 'U1', 't': 1792381765.2462862, 'since': '2026-10-19T03:49:25Z'} | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusOpenExchange` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `WeilConjectures` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |
| `WeilConjectures.PoincareDuality.ProjectionFormula` | unclaimed | Unchanged exported declarations and meanings; no adaptation. |

## Status

landed 20261020T221318-L-4172674 2026-10-20 (merge of deliver/R1/Sheaf.Paper.FiniteReductionConstructibility)
