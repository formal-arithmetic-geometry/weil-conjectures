# Explicit iterated complex endpoints in CompletionMateComparison

## Reason

The finite compatibility proof repeatedly compared a complex of a composite functor with an iterated complex functor by definitional equality. This reconstructed the large quotient-tower and algebraic inverse-image data and exceeded the single-file compile budget. The repair represents these comparisons by explicit natural isomorphisms with iterated endpoints. The module inverse-image functor `Morphism.modulePull` stays the unchanged `abbrev` of the base (reviewer correction, 2026-10-21: the delivered change to a regular `def` broke instance search for `(f.modulePull A).Additive` in `Sheaf.Paper.OrientedNearbyCycles`, whose `tensorEdge` states the categories through `tensorCorner` projections; restoring the `abbrev` costs no measurable compile time). A proved additivity instance `Morphism.modulePull_additive` names the interface used by the explicit comparison. The strict reduction complex comparison declares its iterated result type explicitly, so its use does not need to reconstruct that type from the full construction. It changes no target statement and adds no proof hole.

The repaired module is unclaimed (no claim record at preparation). No adopted-source module is edited. `mapComplexSquare_hom` proves that the lifted square has the old hom component. `quotientEvaluationComplexIso_hom_f` proves that the inserted finite evaluation comparison is the identity in every degree. Hence the old and new normalizations specify the same maps, including level zero and zero/unit ideals. Definitions used by targets changed syntactically, so the affected target statement review must be reopened to confirm this equivalence.

The module adds a public import of `Sheaf.Paper.QuotientTowerEvaluationComplex`, since its comparison occurs in public normalization definitions. All previous public imports are retained.

## Old

```lean
abbrev Morphism.modulePull {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : V.modules A ⥤ U.modules A :=
  ConstantCompletion.pull f.algebra (ConstantCompletion.constantMap f.algebra A)
```

```lean
def Morphism.moduleReductionPullComplexIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) :=
  letI := f.moduleReductionPull_preservesZero A I
  NatIso.mapHomologicalComplex (f.moduleReductionPullIso A I) (.up ℤ)
```

```lean
def Site.finiteEvaluationIso_normalized (T : Site.{u}) (A : Type u)
    [CommRing A] (I : Ideal A) (n : ℕ)
    (e : T.reduction A I ⋙ T.evaluate A n ≅
        T.finiteReduction A I n ⋙ T.finiteRestriction A I n) : Prop :=
  ∀ P : CochainComplex (T.modules A) ℤ, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, (P.X q).IsFlat) →
    e.hom.app ((ConstantCompletion.Q (T.ring A)).obj P) ≫
      (T.finiteRestriction A I n).map
        ((ConstantCompletion.extendComparison
          (ConstantCompletion.quotient T.topology A I n)).app P) =
    (T.evaluate A n).map
        ((ConstantCompletion.quotientPresentation T.topology A I false).comparison.app P) ≫
      (T.evaluateModule A n).mapDerivedCategoryFactors.hom.app
        (ConstantCompletion.reductionComplex T.topology A I false P) ≫
      (ConstantCompletion.resFactors (ConstantCompletion.quotient T.topology A I n)).hom.app
        (((ConstantCompletion.change (ConstantCompletion.quotient T.topology A I n)
          ).mapHomologicalComplex (.up ℤ)).obj P)
```

```lean
def Morphism.finitePullIso_normalized {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (e : f.pull A ⋙ U.finiteReduction A I n ≅
        V.finiteReduction A I n ⋙ f.pull (quotientRing A I n)) : Prop :=
  ∀ P : CochainComplex (V.modules A) ℤ, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, (P.X q).IsFlat) →
    (U.finiteReduction A I n).map ((f.modulePull A).mapDerivedCategoryFactors.hom.app P) ≫
      (ConstantCompletion.extendComparison (ConstantCompletion.quotient U.topology A I n)).app
        (((f.modulePull A).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (ConstantCompletion.Q (U.ring (quotientRing A I n))).map
        ((NatIso.mapHomologicalComplex
          (ConstantCompletion.ordinaryFinitePull f.algebra f.direct f.adjunction A I n)
          (.up ℤ)).hom.app P) =
    e.hom.app ((ConstantCompletion.Q (V.ring A)).obj P) ≫
      (f.pull (quotientRing A I n)).map
        ((ConstantCompletion.extendComparison
          (ConstantCompletion.quotient V.topology A I n)).app P) ≫
      (f.modulePull (quotientRing A I n)).mapDerivedCategoryFactors.hom.app
        (((ConstantCompletion.change (ConstantCompletion.quotient V.topology A I n)
          ).mapHomologicalComplex (.up ℤ)).obj P)
```

## New

```lean
abbrev Morphism.modulePull {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : V.modules A ⥤ U.modules A :=
  ConstantCompletion.pull f.algebra (ConstantCompletion.constantMap f.algebra A)

/-- Additivity of the constant-coefficient inverse image, as a named instance.
Source: Stacks 099N, 03D2 (blueprint: lem-sp-completion-mate-comparison).
Proof: unfold the specified inverse image. Scalar extension and ringed inverse image
are additive, so the existing additive-functor instance applies. -/
instance Morphism.modulePull_additive {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : (f.modulePull A).Additive := by
  dsimp only [Morphism.modulePull]
  infer_instance
```

```lean
def Morphism.moduleReductionPullComplexIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) :
    (ConstantCompletion.reductionTower V.topology A I false).mapHomologicalComplex (.up ℤ) ⋙
        (f.towerModulePull A).mapHomologicalComplex (.up ℤ) ≅
      (f.modulePull A).mapHomologicalComplex (.up ℤ) ⋙
        (ConstantCompletion.reductionTower U.topology A I false).mapHomologicalComplex (.up ℤ) :=
  letI := ConstantCompletion.reductionTower_additive V.topology A I false
  letI := ConstantCompletion.reductionTower_additive U.topology A I false
  letI := f.modulePull_additive A
  ConstantCompletion.mapComplexSquare
    (C := V.modules A) (D := V.towers A) (D' := U.modules A) (E := U.towers A)
    (ConstantCompletion.reductionTower V.topology A I false) (f.towerModulePull A)
    (f.modulePull A) (ConstantCompletion.reductionTower U.topology A I false)
    (f.moduleReductionPullIso A I)
```

```lean
def Site.finiteEvaluationIso_normalized (T : Site.{u}) (A : Type u)
    [CommRing A] (I : Ideal A) (n : ℕ)
    (e : T.reduction A I ⋙ T.evaluate A n ≅
        T.finiteReduction A I n ⋙ T.finiteRestriction A I n) : Prop :=
  ∀ P : CochainComplex (T.modules A) ℤ, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, (P.X q).IsFlat) →
    e.hom.app ((ConstantCompletion.Q (T.ring A)).obj P) ≫
      (T.finiteRestriction A I n).map
        ((ConstantCompletion.extendComparison
          (ConstantCompletion.quotient T.topology A I n)).app P) =
    (T.evaluate A n).map
        ((ConstantCompletion.quotientPresentation T.topology A I false).comparison.app P) ≫
      ((T.evaluateModule A n).mapDerivedCategoryFactors.hom.app
          (ConstantCompletion.reductionComplex T.topology A I false P) ≫
        (ConstantCompletion.Q (T.ring A)).map
          ((ConstantCompletion.quotientEvaluationComplexIso T.topology A I n).hom.app P)) ≫
      (ConstantCompletion.resFactors (ConstantCompletion.quotient T.topology A I n)).hom.app
        (((ConstantCompletion.change (ConstantCompletion.quotient T.topology A I n)
          ).mapHomologicalComplex (.up ℤ)).obj P)
```

```lean
def Morphism.finitePullIso_normalized {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (e : f.pull A ⋙ U.finiteReduction A I n ≅
        V.finiteReduction A I n ⋙ f.pull (quotientRing A I n)) : Prop :=
  ∀ P : CochainComplex (V.modules A) ℤ, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, (P.X q).IsFlat) →
    (U.finiteReduction A I n).map ((f.modulePull A).mapDerivedCategoryFactors.hom.app P) ≫
      (ConstantCompletion.extendComparison (ConstantCompletion.quotient U.topology A I n)).app
        (((f.modulePull A).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (ConstantCompletion.Q (U.ring (quotientRing A I n))).map
        ((ConstantCompletion.mapComplexSquare (f.modulePull A)
          (ConstantCompletion.change (ConstantCompletion.quotient U.topology A I n))
          (ConstantCompletion.change (ConstantCompletion.quotient V.topology A I n))
          (f.modulePull (quotientRing A I n))
          (ConstantCompletion.ordinaryFinitePull f.algebra f.direct f.adjunction A I n)
          ).hom.app P) =
    e.hom.app ((ConstantCompletion.Q (V.ring A)).obj P) ≫
      (f.pull (quotientRing A I n)).map
        ((ConstantCompletion.extendComparison
          (ConstantCompletion.quotient V.topology A I n)).app P) ≫
      (f.modulePull (quotientRing A I n)).mapDerivedCategoryFactors.hom.app
        (((ConstantCompletion.change (ConstantCompletion.quotient V.topology A I n)
          ).mapHomologicalComplex (.up ℤ)).obj P)
```

## Users

Read-only `tools/downstream.py` found the 90 downstream modules below. Its `--uses` scan of the three complex-comparison names found each only in `Sheaf.Paper.CompletionMateComparison` itself (two mentions apiece). A separate name scan across both library roots agreed. The modulePull name itself has existing consumers; its declaration (an `abbrev`, type and body) is unchanged, and its additivity is now also exposed by a proved named instance. The direct importers `Sheaf.Paper.OrientedNearbyCycles` and `Sheaf.Paper.ProEtaleConstantReductionTower`, and the modulePull user `Sheaf.Paper.CompletedProjectionCoherence`, compile unchanged against the repaired module. No external consumer adaptation is included; the declarations keep the same mathematical meaning. Newly added `ReductionPullFiniteEvaluation` uses the explicit comparisons and is part of this packet.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CompletionMateComparison` | unclaimed | Definition representation repair; existing postponed proofs retained. |
| `Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.ExcellentBaseGenericCurvePreparation` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.ExceptionalContractionDiamond` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.FiniteBirationalNodalConnectedIso` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.GeometricSpecializationCategory` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.MultipointedCurveModification` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.OrdinaryMultiplePoint` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.OrdinaryPointDeltaBranches` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.SemistableMultipointedPair` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.StrictlySemistableCurve` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.StrictlySemistableModelNormal` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.AlgebraicGeometry.ValuationStableBlowdownUniqueness` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.CategoryTheory.Sites.CoherentConservativeReflection` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.CategoryTheory.Sites.CoherentEpimorphicQuotient` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.CategoryTheory.Sites.CoherentObjectApproximation` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.CategoryTheory.Sites.CoherentToposRepair` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.CategoryTheory.Sites.FiniteCoproductToposCoherent` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.CategoryTheory.Sites.FiniteLocallyConstantCoherent` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.CategoryTheory.Sites.OrientedAffineSliceSite` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.AlterationBlowupFinite` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.AlterationFiniteRefinement` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.CoherentSetCriterion` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.CompletedProjectionCoherence` | D2 | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.CompletedPullbackUnitTower` | V1 | Item proofs completed; new helpers use the explicit comparison API. |
| `Sheaf.Paper.GeneralNearbySliceTest` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.ModificationClosedImageLifting` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.ModificationsZariskiRefinement` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.NearbyClosedImage` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.NearbyGeometricSlice` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.NearbyProperHyperdescent` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.NearbySpreadOut` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.OrgogozoInductionData` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.OrientedClosedBaseRestriction` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.OrientedConstructibleCoherent` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.OrientedConstructibleSetSheaf` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.OrientedConstructibleSheaf` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.OrientedConstructibleSheafVanishing` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.OrientedConstructibleSubquotients` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.OrientedHypercoverDescentDatum` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.OrientedMaximalPointFiniteness` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.OrientedNearbyCycles` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.OrientedProductPointsConservative` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.OrientedProperFibreExchange` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.OrientedSourceLocalization` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.ProEtaleConstantReductionTower` | T1 | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.PsiConstructibilityDescent` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.StratifiedOrientedCover` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.SixFunctors.TraceFormula.NodalEtaleChart` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.SixFunctors.TraceFormula.NodalLogRegularity` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.ClosedImageGenericAlteration` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.ContractedComponentGenericData` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.ContractedComponentNoExtraGeneric` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.CurveP1TreeLocalCriterion` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.FinitarySiteCoherentGenerators` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.FiniteEtaModificationGluing` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.FiniteFibreValuationDomination` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.LocalMarkingLength` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.MarkedCurveFiniteTypeModel` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.NodalContractionNormalizationBranches` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.OrientedPointCohomology` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.OrientedPointNormalizedStratum` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.ProjectiveLineTree` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.ProperBaseChangeCoherentConservative` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.ReducedFibreModification` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.SemistableMarkedPoint` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.SemistableModificationFibreContractions` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.SemistableNormalTargetFactorization` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.SingleValuationSemistableExtraction` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.StableModificationStabilityFieldDescent` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.ValuationCurveProjectivePreparation` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.ValuationExceptionalLocalCriterion` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.ValuationHorizontalCurveModels` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.ValuationModificationProperCompletion` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.ValuationNormalizedGraphModel` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.ValuationReducedFibreNormalization` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.ValuationStrictSemistableCofinality` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.TraceFormula.ValuationSymmetricNodalBlowup` | unclaimed | No adaptation; comparisons have identical degreewise maps. |
| `Sheaf.Paper.ReductionPullFiniteEvaluation` | V1 (new) | New proof uses explicit comparison equations. |
| `Sheaf.Paper.CompletionUnitFiniteProjection` | V1 (new) | Uses the proved identity-chain-map formula in the normalized projection proof. |
| `Sheaf.Paper.CompletionFiniteReduction` | V1 (new) | Uses the preceding projection theorem; no further normalization change. |

## Status

landed 20261021T021030-L-2694797 2026-10-21 (merge of deliver/V1/Sheaf.Paper.CompletedPullbackUnitTower)
