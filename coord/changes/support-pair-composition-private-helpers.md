# Private composition helpers and their scoped section-variable exclusions

## Reason

The proof adds two proved private helpers. Each uses `omit ... in` to exclude the
three unused `HasSheafify` section assumptions from that helper alone. The static
interface checker counts these scoped commands as an interface change, so this
record documents them explicitly. Neither command applies to any existing public
declaration. All existing public signatures, visibility, definitions, imports and
instance registrations are identical. The theorem proof changes from `sorry` to
a proof from the already stated chain-coherence theorem.

## Old

Neither private helper existed, and there were no scoped `omit` commands here.
All existing public declarations retain their original signatures and visibility.

## New

The new private declarations, including the scope of each command, are:

```lean
omit [HasSheafify Jc AddCommGrpCat.{w₀}] [HasSheafify Jd AddCommGrpCat.{w₀}]
  [HasSheafify Je AddCommGrpCat.{w₀}] in
private theorem adjointSection_comp
    (u : C ⥤ D) (v : D ⥤ E) [u.IsContinuous Jc Jd] [v.IsContinuous Jd Je]
    (L : Sheaf Jc AddCommGrpCat.{w₀} ⥤ Sheaf Jd AddCommGrpCat.{w₀})
    (M : Sheaf Jd AddCommGrpCat.{w₀} ⥤ Sheaf Je AddCommGrpCat.{w₀})
    (adjL : L ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd)
    (adjM : M ⊣ v.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jd Je)
    (F : Sheaf Jc AddCommGrpCat.{w₀}) (G : Sheaf Jd AddCommGrpCat.{w₀})
    (H : Sheaf Je AddCommGrpCat.{w₀}) (h : L.obj F ⟶ G) (k : M.obj G ⟶ H)
    (T : C) (T' : D) (T'' : E) (t : T' ⟶ u.obj T) (t' : T'' ⟶ v.obj T') :
    (sectionFunctor Jc T).map ((adjL.comp adjM).homEquiv F H (M.map h ≫ k)) ≫
        (sectionRestriction Je (t' ≫ v.map t)).app H =
      ((sectionFunctor Jc T).map (adjL.homEquiv F G h) ≫
        (sectionRestriction Jd t).app G) ≫
      ((sectionFunctor Jd T').map (adjM.homEquiv G H k) ≫
        (sectionRestriction Je t').app H) := by
  rw [Adjunction.comp_homEquiv]
  change (sectionFunctor Jc T).map
    (adjL.homEquiv F _ (adjM.homEquiv _ H (M.map h ≫ k))) ≫ _ = _
  rw [adjM.homEquiv_naturality_left, adjL.homEquiv_naturality_right,
    Functor.map_comp]
  change ((adjL.homEquiv F G h).hom.app (Opposite.op T) ≫
      (adjM.homEquiv G H k).hom.app (Opposite.op (u.obj T))) ≫
      H.obj.map (t' ≫ v.map t).op = _
  simp only [op_comp, H.obj.map_comp, Category.assoc]
  have hn := (adjM.homEquiv G H k).hom.naturality t.op
  change G.obj.map t.op ≫ (adjM.homEquiv G H k).hom.app (Opposite.op T') =
    (adjM.homEquiv G H k).hom.app (Opposite.op (u.obj T)) ≫
      H.obj.map (v.map t).op at hn
  change _ = ((adjL.homEquiv F G h).hom.app (Opposite.op T) ≫ G.obj.map t.op) ≫
    ((adjM.homEquiv G H k).hom.app (Opposite.op T') ≫ H.obj.map t'.op)
  rw [Category.assoc, ← Category.assoc (G.obj.map t.op), hn]
  simp only [Category.assoc]

omit [HasSheafify Jc AddCommGrpCat.{w₀}] [HasSheafify Jd AddCommGrpCat.{w₀}]
  [HasSheafify Je AddCommGrpCat.{w₀}] in
private theorem supportPair_comp_condition
    (u : C ⥤ D) (v : D ⥤ E) [u.IsContinuous Jc Jd] [v.IsContinuous Jd Je]
    (L : Sheaf Jc AddCommGrpCat.{w₀} ⥤ Sheaf Jd AddCommGrpCat.{w₀})
    (M : Sheaf Jd AddCommGrpCat.{w₀} ⥤ Sheaf Je AddCommGrpCat.{w₀})
    (adjL : L ⊣ u.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jc Jd)
    (adjM : M ⊣ v.sheafPushforwardContinuous AddCommGrpCat.{w₀} Jd Je)
    [L.Additive] [M.Additive]
    (P : SupportPair (C := C)) (P' : SupportPair (C := D))
    (P'' : SupportPair (C := E))
    (t : P'.T ⟶ u.obj P.T) (s : P'.V ⟶ u.obj P.V)
    (t' : P''.T ⟶ v.obj P'.T) (s' : P''.V ⟶ v.obj P'.V)
    {I : CochainComplex (Sheaf Jc AddCommGrpCat.{w₀}) ℤ}
    {K : CochainComplex (Sheaf Jd AddCommGrpCat.{w₀}) ℤ}
    {N : CochainComplex (Sheaf Je AddCommGrpCat.{w₀}) ℤ}
    (h : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ K)
    (k : (M.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ N)
    (φ : supportDiagram Jc P I ⟶ supportDiagram Jd P' K)
    (ψ : supportDiagram Jd P' K ⟶ supportDiagram Je P'' N)
    (hφ : supportPairMapCondition Jc Jd u L adjL P P' t s h φ)
    (hψ : supportPairMapCondition Jd Je v M adjM P' P'' t' s' k ψ) :
    compositeSupportPairMapCondition Jc Jd Je u v L M adjL adjM P P''
      (t' ≫ v.map t) (s' ≫ v.map s)
      ((M.mapHomologicalComplex (ComplexShape.up ℤ)).map h ≫ k) (φ ≫ ψ) := by
  constructor
  · intro n
    change φ.τ₂.f n ≫ ψ.τ₂.f n = _
    rw [hφ.1 n, hψ.1 n]
    exact (adjointSection_comp Jc Jd Je u v L M adjL adjM
      (I.X n) (K.X n) (N.X n) (h.f n) (k.f n) P.T P'.T P''.T t t').symm
  · intro n
    change φ.τ₃.f n ≫ ψ.τ₃.f n = _
    rw [hφ.2 n, hψ.2 n]
    exact (adjointSection_comp Jc Jd Je u v L M adjL adjM
      (I.X n) (K.X n) (N.X n) (h.f n) (k.f n) P.V P'.V P''.V s s').symm
```

## Users

The source-only downstream scan lists the modules below. Its `--uses
supportPairComposition` scan finds only the item's own declaration: current
consumers import its API and definitions, without directly applying this theorem.
None needs adaptation: the commands scope only over the immediately following
private declaration, and every existing public declaration is unchanged. No target
statement or the meaning of any definition changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SupportPairComposition | X2 | Add private helpers; fill theorem proof; public API unchanged. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | No change; no adaptation required. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | No change; no adaptation required. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | No change; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | No change; no adaptation required. |
| Sheaf.AlgebraicGeometry.PunctualStrictCompletionTest | unclaimed | No change; no adaptation required. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | S1 | No change; no adaptation required. |
| Sheaf.AlgebraicGeometry.StrictLocalEtaleDimensionBounds | unclaimed | No change; no adaptation required. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | A3 | No change; no adaptation required. |
| Sheaf.AlgebraicGeometry.SupportLongExact | A4 | No change; no adaptation required. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | S2 | No change; no adaptation required. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | No change; no adaptation required. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No change; no adaptation required. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | No change; no adaptation required. |
| Sheaf.Paper.AdicPurityObjects | W9 | No change; no adaptation required. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | No change; no adaptation required. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | No change; no adaptation required. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | No change; no adaptation required. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | G6 | No change; no adaptation required. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.CompletionSupportedConstantComparison | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | No change; no adaptation required. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | No change; no adaptation required. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | No change; no adaptation required. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | No change; no adaptation required. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | No change; no adaptation required. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | No change; no adaptation required. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.PurAdicReconstruction | H8 | No change; no adaptation required. |
| Sheaf.Paper.PurityAffineLineOrientation | J6 | No change; no adaptation required. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | E2 | No change; no adaptation required. |
| Sheaf.Paper.PurityChernClasses | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | F1 | No change; no adaptation required. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | No change; no adaptation required. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.PurityDncComparisons | G3 | No change; no adaptation required. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | E3 | No change; no adaptation required. |
| Sheaf.Paper.PurityDncInvariance | H2 | No change; no adaptation required. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.PurityGysinStructure | F1 | No change; no adaptation required. |
| Sheaf.Paper.PurityRankOneLocalCalculation | F2 | No change; no adaptation required. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 | No change; no adaptation required. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | No change; no adaptation required. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | No change; no adaptation required. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.SmoothPurityMap | R2 | No change; no adaptation required. |
| Sheaf.Paper.SmoothTrace | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.SupportedHomPullback | H4 | No change; no adaptation required. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | No change; no adaptation required. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.WeilFourierInversion | J6 | No change; no adaptation required. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.WeilOne | unclaimed | No change; no adaptation required. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No change; no adaptation required. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | No change; no adaptation required. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | No change; no adaptation required. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No change; no adaptation required. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No change; no adaptation required. |
| TargetsCheck | unclaimed | No change; no adaptation required. |
| WeilConjectures | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | Z8 | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | B4 | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No change; no adaptation required. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | No change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | No change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | No change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | No change; no adaptation required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | No change; no adaptation required. |
| WeilConjectures.Statement | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | C1 | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | C3 | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | D2 | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | No change; no adaptation required. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | No change; no adaptation required. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No change; no adaptation required. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No change; no adaptation required. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No change; no adaptation required. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No change; no adaptation required. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No change; no adaptation required. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No change; no adaptation required. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No change; no adaptation required. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No change; no adaptation required. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No change; no adaptation required. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | No change; no adaptation required. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No change; no adaptation required. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No change; no adaptation required. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No change; no adaptation required. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No change; no adaptation required. |
| WeilConjectures.ZetaFunction.TraceFormula | X5 | No change; no adaptation required. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No change; no adaptation required. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No change; no adaptation required. |

## Status

landed 20261019T112614-L-3961247 2026-10-19 (merge of deliver/X2/Sheaf.Paper.SupportPairComposition)
