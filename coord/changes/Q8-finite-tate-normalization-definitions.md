# Finite Tate normalization definitions

## Reason

Separate the original normalization definitions from the theorem that uses them, so the
normalized-comparison and coherence lemmas can refer to the predicates without an import cycle.
This is a dependency extraction for the mathematical decomposition, not a compilation timeout
workaround. The target statement and all twelve definition signatures and bodies are unchanged.
No source-library declaration is edited.

## Old

The twelve declarations were defined directly in
`lean/Sheaf/Paper/FiniteTateSiteDescent.lean`:

```lean
namespace AlgebraicGeometry.Scheme

/-- The existing finite quotient ring, lifted only to the sheaf universe.
Source: coefficient notation (blueprint: lem-amb-finite-tate-site-descent). -/
abbrev finiteTateCoefficient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :=
  ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (n : ℕ) (T : Scheme.{u})

/-- Restrict the recorded finite Tate module to its constant scalar action.
Source: Stacks Tag 03CY (blueprint: lem-amb-finite-tate-site-descent). -/
def finiteTateConstantRestriction :
    SheafOfModules.{u + 1} (integralCoefficientSheaf l E T n) ⥤
      Sheaf (ProEt.topology T)
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) :=
  letI := purTwistForgetPreservesSheafification T
  SheafOfModules.restrictScalars
      ((constantCommuteCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
          (CommRingCat.of (finiteTateCoefficient l E n))).inv ⋙
    constantRingModuleRestriction (ProEt.topology T) (finiteTateCoefficient l E n)

/-- The original finite pro-etale twist, in the fixed-coefficient encoding.
Source: coefficient-twist blueprint, order 1505
(blueprint: lem-amb-finite-tate-site-descent). -/
abbrev finiteTateProSheaf (a : ℕ) :=
  (finiteTateConstantRestriction l E n T).obj (finiteCoefficientTwist l E T n (a : ℤ))

/-- A sectionwise pure tensor in the first finite twist.
Source: Stacks Tag 03EK (blueprint: lem-amb-finite-tate-site-descent). -/
def finiteTateProGenerator (W : T.ProEtᵒᵖ)
    (a : finiteTateCoefficient l E n)
    (x : (purTwistZlOne T l).obj.obj W) :
    (finiteTateProSheaf l E n T 1).obj.obj W :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (integralCoefficientSheaf l E T n).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
        (purTwistIntegralQuotient T l E n) (purTwistIntegralOne T l E))).app W)
    (((realizationRingUnit (ProEt.topology T)
      (finiteTateCoefficient l E n)).app W a) ⊗ₜ[_,
        ((purTwistIntegralQuotient T l E n).hom.app W).hom]
      (purTwistIntegralTensor T l E W 1 x))

/-- Pure local tensors in the prescribed nonnegative pro-etale powers.
Source: Stacks Tag 03EK (blueprint: lem-amb-finite-tate-site-descent). -/
def finiteTateProPowerGenerator (W : T.ProEtᵒᵖ)
    (a : finiteTateCoefficient l E n) :
    (k : ℕ) → (Fin k → (purTwistZlOne T l).obj.obj W) →
      (finiteTateProSheaf l E n T k).obj.obj W
  | 0, _ => (realizationRingUnit (ProEt.topology T)
      (finiteTateCoefficient l E n)).app W a
  | 1, x => finiteTateProGenerator l E n T W a (x 0)
  | k + 2, x => SheafOfModules.siteSheafTensorTmul
      (coefficientTwistPower T (purTwistFiniteOne T l E n) (k + 1))
      (purTwistFiniteOne T l E n) W
      (finiteTateProPowerGenerator W a (k + 1) (fun i ↦ x i.castSucc))
      (finiteTateProGenerator l E n T W 1 (x (Fin.last (k + 1))))

/-- Pure local tensors in the recorded etale Tate powers.
Source: Stacks Tags 03PK and 03EK (blueprint: lem-amb-finite-tate-site-descent). -/
def finiteTateEtalePowerGenerator (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (W : T.Etaleᵒᵖ) (a : A) :
    (k : ℕ) → (Fin k → (T.rootsOfUnitySheaf m).obj.obj W) →
      (finiteEtaleTateTwist T m A hA k).obj.obj W
  | 0, _ => (toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a
  | 1, x => finiteEtaleTateOneGenerator A m T hA W a (x 0)
  | k + 2, x =>
      (Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
        (finiteEtaleTateTwist T m A hA (k + 1)) (finiteEtaleTateLine T m A hA)).app W
        (finiteTateEtalePowerGenerator A m hA W a (k + 1) (fun i ↦ x i.castSucc) ⊗ₜ[A]
          finiteEtaleTateOneGenerator A m T hA W 1 (x (Fin.last (k + 1))))

/-- The actual unit underlying a finite root section on the etale site.
Source: Stacks Tag 03PK (blueprint: lem-amb-finite-tate-site-descent). -/
def finiteTateEtaleRootValue (m : ℕ) (W : T.Etaleᵒᵖ)
    (z : (T.rootsOfUnitySheaf m).obj.obj W) : Γ(W.unop.left, ⊤)ˣ :=
  Additive.toMul (((kernel.ι (m • 𝟙 T.gmSheaf)).hom.app W z).down)

/-- The actual unit in a specified projection of the root limit.
Source: Stacks Tag 03PK (blueprint: lem-amb-finite-tate-site-descent). -/
def finiteTateLimitRootValue (r : ℕ) (W : T.ProEtᵒᵖ)
    (x : (purTwistZlOne T l).obj.obj W) : Γ(W.unop.left, ⊤)ˣ :=
  Additive.toMul (((proEtaleRootsOfUnityInclusion T (l ^ (r + 1))).hom.app W
    ((limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op r)).hom.app W x)).down)

/-- Root-projection normalization of the comparison, on every local pure tensor.
The arrow `f` allows arbitrary pro-etale tests over an etale object, so roots may be
lifted to the infinite root tower pro-etale locally, without requiring an etale lift.
Source: Stacks Tags 03PK and 0GLZ
(blueprint: lem-amb-finite-tate-site-descent). -/
def IsFiniteTateSiteComparison (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ)
    (b : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
        (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅ finiteTateProSheaf l E n T k) : Prop :=
  ∀ (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (f : W.unop ⟶ (toProEt T).obj U.unop)
    (a : finiteTateCoefficient l E n)
    (z : Fin k → (T.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj U)
    (x : Fin k → (purTwistZlOne T l).obj.obj W),
    (∀ i : Fin k, finiteTateLimitRootValue l T r W (x i) =
      Units.map f.left.appTop.hom.toMonoidHom (finiteTateEtaleRootValue T (l ^ (r + 1)) U (z i))) →
    b.hom.hom.app W
      (((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
          (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k)).obj.map f.op
        (((ProEtale.comparisonAdjunction
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).unit.app
            (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k)).hom.app U
              (finiteTateEtalePowerGenerator T _ (l ^ (r + 1)) hA U a k z))) =
      finiteTateProPowerGenerator l E n T W a k x

/-- The pullback comparison on etale powers is fixed on root tensors.
Source: Stacks Tags 03PK and 03Q1
(blueprint: lem-amb-finite-tate-site-descent). -/
def IsFiniteTateEtalePullback {T' : Scheme.{u}} (v : T' ⟶ T) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ)
    (c : (Etale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).obj
      (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅
        finiteEtaleTateTwist T' (l ^ (r + 1)) _ hA k) : Prop :=
  ∀ (U : T.Etaleᵒᵖ) (a : finiteTateCoefficient l E n)
    (z : Fin k → (T.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj U)
    (z' : Fin k → (T'.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj
      ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj U)),
    (∀ i : Fin k,
      finiteTateEtaleRootValue T' (l ^ (r + 1)) _ (z' i) =
        Units.map (pullback.fst U.unop.hom v).appTop.hom.toMonoidHom
          (finiteTateEtaleRootValue T (l ^ (r + 1)) U (z i))) →
    ((Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).homEquiv _ _ c.hom).hom.app U
        (finiteTateEtalePowerGenerator T _ (l ^ (r + 1)) hA U a k z) =
      finiteTateEtalePowerGenerator T' _ (l ^ (r + 1)) hA _ a k z'

/-- The usual pro-etale pullback comparison, fixed by every root projection.
Source: Stacks Tag 09A5; the root tower limit universal property
(blueprint: lem-amb-finite-tate-site-descent). -/
def IsFiniteTateProPullback {T' : Scheme.{u}} (v : T' ⟶ T) (k : ℕ)
    (b : (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).obj
      (finiteTateProSheaf l E n T k) ≅ finiteTateProSheaf l E n T' k) : Prop :=
  ∀ (U : T.ProEtᵒᵖ) (a : finiteTateCoefficient l E n)
    (x : Fin k → (purTwistZlOne T l).obj.obj U)
    (x' : Fin k → (purTwistZlOne T' l).obj.obj
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ v).op.obj U)),
    (∀ (s : ℕ) (i : Fin k), finiteTateLimitRootValue l T' s _ (x' i) =
      Units.map (pullback.fst U.unop.hom v).appTop.hom.toMonoidHom
        (finiteTateLimitRootValue l T s U (x i))) →
    ((ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).homEquiv _ _ b.hom).hom.app U
        (finiteTateProPowerGenerator l E n T U a k x) =
      finiteTateProPowerGenerator l E n T' _ a k x'

/-- The exponent-change comparison is induced by the specified root power map.
Source: Stacks Tag 03PK (blueprint: lem-amb-finite-tate-site-descent). -/
def IsFiniteTateEtaleTransition (r r' : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (hA' : ((l ^ (r' + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ)
    (t : finiteEtaleTateTwist T (l ^ (r' + 1)) _ hA' k ≅
      finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) : Prop :=
  ∀ (U : T.Etaleᵒᵖ) (a : finiteTateCoefficient l E n)
    (z' : Fin k → (T.rootsOfUnitySheaf (l ^ (r' + 1))).obj.obj U)
    (z : Fin k → (T.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj U),
    (∀ i : Fin k, finiteTateEtaleRootValue T (l ^ (r + 1)) U (z i) =
      finiteTateEtaleRootValue T (l ^ (r' + 1)) U (z' i) ^ (l ^ (r' - r))) →
    t.hom.hom.app U (finiteTateEtalePowerGenerator T _ (l ^ (r' + 1)) hA' U a k z') =
      finiteTateEtalePowerGenerator T _ (l ^ (r + 1)) hA U a k z
```

## New

The exact same declaration text is in
`lean/Sheaf/Paper/FiniteTateSiteDescentDefinitions.lean`, with definition-node docstring tags.
The original module publicly imports the new definitions module, which publicly imports the
original eight public dependencies. Thus existing importers see the same interface. A source
comparison with comments removed confirms all twelve bodies and signatures are identical.

## Users

`tools/downstream.py Sheaf.Paper.FiniteTateSiteDescent --uses IsFiniteTateSiteComparison`
listed 230 transitive consumers. Every existing declaration remains available by its original
name through the original module. No consumer adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteTateSiteDescent | Q8 | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerData | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerDescent | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerNaturality | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AffineCoefficientCounitMaps | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AffineCoefficientCounitNormalization | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AffineDiagonalIntegrationOrientation | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AffineDiagonalTateCoordinates | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AffineLineCompositeTranspose | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AffineLinePuritySource | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AffineSpacePurityComposition | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceThomMap | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AffineTowerIntegrationSiteTransport | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AffineTranslationTrace | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.BaseChangedLineTraceEvaluation | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.BrownTowerBoundedTransport | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | U5 | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.BrownTowerRealization | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.BrownTowerSite | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.CanonicalTateArrowNaturality | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.CanonicalTateComparisons | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.CartierRelativeKummerRealization | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ChartCounitScalarTransport | M9 | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ChartDncVectorFactors | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ClopenCanonicalFiniteEvaluation | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ClopenSystemFiniteRealization | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ClopenSystemRestrictionEvaluation | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.CondensedTateIntegralTower | F4 | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalMateCocycles | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.CoordinateLineAdjunction | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.CoordinateLineAdjunctionMaps | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.CoordinateProductPresentations | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.CoordinateSectionArrows | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.CoordinateSectionProductRecursion | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.CoordinateSectionProjection | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.CoordinateZeroBaseChange | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceCoordinates | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceSiteComparison | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.DiagonalDncChartNormalization | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.DiagonalOrientationRefinement | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.DualityPullback | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | W6 | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | Y6 | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | P8 | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | F2 | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteSiteCoordinates | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteTateBalancedScalarPullback | H2 | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteTateScalarSourceNormalization | G3 | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteTwistRootTrivialization | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FormalVerdierExchangeEquivariance | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.GeneralChartComparisons | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.IntegrationExponentTransposeTransport | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.LineKummerFieldRealization | J9 | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.OrderedTateScalarNormalization | H4 | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.OrientedPerfectDuality | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.P1CounitScalar | F4 | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.P1KummerTraceSiteTransport | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.PairingData | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.PodMixedSupportCupProduct | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.PointSignedCyclotomicAction | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.PointTateFiberCoefficientComparisons | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleAffineLineCounit | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleFrameIntegration | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleOrderedIntegration | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionIntegration | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProjectiveCoefficient | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleVectorIntegration | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleVectorIntegrationArrows | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ProjectionPurityAgreement | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.RawChartScalarCounitPasting | P6 | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.SignedTwistSiteTransport | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOrientation | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.SupportedProjectiveChern | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.VectorIntegrationChartComparison | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.VectorTensorSiteEquations | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.VectorTraceScalarDescent | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.WfTateTwist | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | Existing public names, signatures, and bodies reexported unchanged; no adaptation. |

## Status

landed 20261025T003330-L-3230059 2026-10-25 (merge of deliver/Q8/Sheaf.Paper.FiniteTateSiteDescent)
