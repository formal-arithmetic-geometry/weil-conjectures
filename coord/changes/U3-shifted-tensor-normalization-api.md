# Shifted tensor normalization API

## Reason

Complete the unique canonical two-shift comparison without repeatedly elaborating
the total coproduct construction in concrete sheaf formulas. The comparison is still
the second shift first, then the first shift, with the original localization square.
The normalization predicates factor the exact same quantified equations through
generic categories and functors; no hypothesis or conclusion changes mathematically.

`ShiftedTensorModel` becomes an abbreviation of the generic structure
`ResolvingTensorModel`; its two data fields are still `tensor` and `representative`
with the original types. Consumers using named-field structure syntax retain it.
No current consumer refers to `ShiftedTensorModel.mk`, `.rec`, or generated extensionality
declarations. The replacement does remove those unused generated declaration names;
this is an interface change requiring independent review.

The chosen canonical maps still come from the same unique-normalization propositions.
The source library and `Challenge.lean` are untouched. Targets whose meaning is
transitively expressed using these definitions are submitted for semantic re-review;
the intended meaning and every displayed equation are preserved.

## Old

```lean
abbrev shiftedTotalTensor := Functor.uncurry.obj ((shiftedOrdinaryTensor R).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))
```

```lean
structure ShiftedTensorModel where tensor : ShiftedDerivedCategory R × ShiftedDerivedCategory R ⥤ ShiftedDerivedCategory R representative : ((shiftedTensorResolving R).ι.prod (shiftedTensorResolving R).ι) ⋙ shiftedTotalTensor R ⋙ DerivedCategory.Q ≅ (((shiftedTensorResolving R).ι ⋙ DerivedCategory.Q).prod ((shiftedTensorResolving R).ι ⋙ DerivedCategory.Q)) ⋙ tensor
```

```lean
def shiftedTensorComplexComparison (E F : CochainComplex (ShiftedModuleCategory R) ℤ) (a b : ℤ) : (shiftedTotalTensor R).obj (E⟦a⟧, F⟦b⟧) ≅ ((shiftedTotalTensor R).obj (E, F))⟦a + b⟧ := letI := monoidalCategory R letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R CochainComplex.mapBifunctorShift₂Iso (E⟦a⟧) F (shiftedOrdinaryTensor R) b ≪≫ (CategoryTheory.shiftFunctor _ b).mapIso (CochainComplex.mapBifunctorShift₁Iso E F (shiftedOrdinaryTensor R) a) ≪≫ (shiftFunctorAdd _ a b).symm.app _
```

```lean
def IsCanonicalShiftComparison (a b : ℤ) (t : ((CategoryTheory.shiftFunctor (ShiftedDerivedCategory R) a).prod (CategoryTheory.shiftFunctor (ShiftedDerivedCategory R) b) ⋙ T.tensor) ≅ T.tensor ⋙ CategoryTheory.shiftFunctor _ (a + b)) : Prop := ∀ (E F : CochainComplex (ShiftedModuleCategory R) ℤ) (hE : shiftedTensorResolving R E) (hF : shiftedTensorResolving R F), ∃ (hEa : shiftedTensorResolving R (E⟦a⟧)) (hFb : shiftedTensorResolving R (F⟦b⟧)), T.representative.hom.app (⟨E⟦a⟧, hEa⟩, ⟨F⟦b⟧, hFb⟩) ≫ T.tensor.map (Prod.mkHom ((DerivedCategory.Q.commShiftIso a).hom.app E) ((DerivedCategory.Q.commShiftIso b).hom.app F)) ≫ t.hom.app (DerivedCategory.Q.obj E, DerivedCategory.Q.obj F) = DerivedCategory.Q.map (shiftedTensorComplexComparison R E F a b).hom ≫ (DerivedCategory.Q.commShiftIso (a + b)).hom.app _ ≫ (CategoryTheory.shiftFunctor _ (a + b)).map (T.representative.hom.app (⟨E, hE⟩, ⟨F, hF⟩))
```

```lean
def IsSignedComplexSwap (E F : CochainComplex (ShiftedModuleCategory R) ℤ) (χ : (shiftedTotalTensor R).obj (E, F) ≅ (shiftedTotalTensor R).obj (F, E)) : Prop := ∀ p q : ℤ, CochainComplex.ιMapBifunctor E F (shiftedOrdinaryTensor R) p q (p + q) rfl ≫ χ.hom.f (p + q) = ((-1 : ℤ) ^ Int.natAbs (p * q)) • (((symmetricCategory R).braiding (E.X p) (F.X q)).hom ≫ CochainComplex.ιMapBifunctor F E (shiftedOrdinaryTensor R) q p (p + q) (add_comm q p))
```

```lean
def IsCanonicalDerivedTensorSymmetry (σ : T.tensor ≅ CategoryTheory.Prod.swap _ _ ⋙ T.tensor) : Prop := ∀ (E F : CochainComplex (ShiftedModuleCategory R) ℤ) (hE : shiftedTensorResolving R E) (hF : shiftedTensorResolving R F), ∃ χ : (shiftedTotalTensor R).obj (E, F) ≅ (shiftedTotalTensor R).obj (F, E), IsSignedComplexSwap R E F χ ∧ T.representative.hom.app (⟨E, hE⟩, ⟨F, hF⟩) ≫ σ.hom.app (DerivedCategory.Q.obj E, DerivedCategory.Q.obj F) = DerivedCategory.Q.map χ.hom ≫ T.representative.hom.app (⟨F, hF⟩, ⟨E, hE⟩)
```

```lean
def IsComplexTensorAssociator (E F G : CochainComplex (ShiftedModuleCategory R) ℤ) (χ : (shiftedTotalTensor R).obj ((shiftedTotalTensor R).obj (E, F), G) ≅ (shiftedTotalTensor R).obj (E, (shiftedTotalTensor R).obj (F, G))) : Prop := ∀ p q r : ℤ, ((shiftedOrdinaryTensor R).map (CochainComplex.ιMapBifunctor E F (shiftedOrdinaryTensor R) p q (p + q) rfl)).app _ ≫ CochainComplex.ιMapBifunctor ((shiftedTotalTensor R).obj (E, F)) G (shiftedOrdinaryTensor R) (p + q) r ((p + q) + r) rfl ≫ χ.hom.f ((p + q) + r) = ((monoidalCategory R).associator (E.X p) (F.X q) (G.X r)).hom ≫ ((shiftedOrdinaryTensor R).obj (E.X p)).map (CochainComplex.ιMapBifunctor F G (shiftedOrdinaryTensor R) q r (q + r) rfl) ≫ CochainComplex.ιMapBifunctor E ((shiftedTotalTensor R).obj (F, G)) (shiftedOrdinaryTensor R) p (q + r) ((p + q) + r) (add_assoc p q r).symm
```

```lean
def IsCanonicalTensorAssociator (α : shiftedTensorLeftTriple R T ≅ shiftedTensorRightTriple R T) : Prop := ∀ (E F G : CochainComplex (ShiftedModuleCategory R) ℤ) (hE : shiftedTensorResolving R E) (hF : shiftedTensorResolving R F) (hG : shiftedTensorResolving R G), ∃ (hEF : shiftedTensorResolving R ((shiftedTotalTensor R).obj (E, F))) (hFG : shiftedTensorResolving R ((shiftedTotalTensor R).obj (F, G))) (χ : (shiftedTotalTensor R).obj ((shiftedTotalTensor R).obj (E, F), G) ≅ (shiftedTotalTensor R).obj (E, (shiftedTotalTensor R).obj (F, G))), IsComplexTensorAssociator R E F G χ ∧ T.representative.hom.app (⟨_, hEF⟩, ⟨G, hG⟩) ≫ T.tensor.map (Prod.mkHom (T.representative.hom.app (⟨E, hE⟩, ⟨F, hF⟩)) (𝟙 (DerivedCategory.Q.obj G))) ≫ α.hom.app ((DerivedCategory.Q.obj E, DerivedCategory.Q.obj F), DerivedCategory.Q.obj G) = DerivedCategory.Q.map χ.hom ≫ T.representative.hom.app (⟨E, hE⟩, ⟨_, hFG⟩) ≫ T.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj E)) (T.representative.hom.app (⟨F, hF⟩, ⟨G, hG⟩)))
```

```lean
def ShiftedPullbackCoherence (μ : T.tensor ⋙ uStar.mapDerivedCategory ≅ (uStar.mapDerivedCategory.prod uStar.mapDerivedCategory) ⋙ TS.tensor) : Prop := (∀ X Y Z : ShiftedDerivedCategory R, uStar.mapDerivedCategory.map ((derivedTensorAssociator R T).hom.app ((X, Y), Z)) ≫ μ.hom.app (X, T.tensor.obj (Y, Z)) ≫ TS.tensor.map (Prod.mkHom (𝟙 (uStar.mapDerivedCategory.obj X)) (μ.hom.app (Y, Z))) = μ.hom.app (T.tensor.obj (X, Y), Z) ≫ TS.tensor.map (Prod.mkHom (μ.hom.app (X, Y)) (𝟙 (uStar.mapDerivedCategory.obj Z))) ≫ (derivedTensorAssociator S TS).hom.app ((uStar.mapDerivedCategory.obj X, uStar.mapDerivedCategory.obj Y), uStar.mapDerivedCategory.obj Z)) ∧ (∀ X Y : ShiftedDerivedCategory R, uStar.mapDerivedCategory.map ((derivedTensorSymmetry R T).hom.app (X, Y)) ≫ μ.hom.app (Y, X) = μ.hom.app (X, Y) ≫ (derivedTensorSymmetry S TS).hom.app (uStar.mapDerivedCategory.obj X, uStar.mapDerivedCategory.obj Y)) ∧ ∀ (a b : ℤ) (X Y : ShiftedDerivedCategory R), uStar.mapDerivedCategory.map ((shiftedTensorCanonicalComparison R T a b).hom.app (X, Y)) ≫ (uStar.mapDerivedCategory.commShiftIso (a + b)).hom.app (T.tensor.obj (X, Y)) ≫ (CategoryTheory.shiftFunctor _ (a + b)).map (μ.hom.app (X, Y)) = μ.hom.app (X⟦a⟧, Y⟦b⟧) ≫ TS.tensor.map (Prod.mkHom ((uStar.mapDerivedCategory.commShiftIso a).hom.app X) ((uStar.mapDerivedCategory.commShiftIso b).hom.app Y)) ≫ (shiftedTensorCanonicalComparison S TS a b).hom.app (uStar.mapDerivedCategory.obj X, uStar.mapDerivedCategory.obj Y)
```

## New

```lean
def shiftedTotalTensor := Functor.uncurry.obj (shiftedOrdinaryTensor R).map₂CochainComplex
```

```lean
abbrev ShiftedTensorModel := ResolvingTensorModel DerivedCategory.Q (shiftedTensorResolving R) (shiftedTotalTensor R)
```

```lean
def shiftedTensorComplexComparison (E F : CochainComplex (ShiftedModuleCategory R) ℤ) (a b : ℤ) : (shiftedTotalTensor R).obj (E⟦a⟧, F⟦b⟧) ≅ ((shiftedTotalTensor R).obj (E, F))⟦a + b⟧ := (shiftedTensorComplexComparisonNatIso R a b).app (E, F)
```

```lean
def IsCanonicalShiftComparison (a b : ℤ) (t : ((CategoryTheory.shiftFunctor (ShiftedDerivedCategory R) a).prod (CategoryTheory.shiftFunctor (ShiftedDerivedCategory R) b) ⋙ T.tensor) ≅ T.tensor ⋙ CategoryTheory.shiftFunctor _ (a + b)) : Prop := TensorShiftNormalization DerivedCategory.Q (shiftedTensorResolving R) (shiftedTotalTensor R) T.tensor T.representative a b (shiftedTensorComplexComparisonNatIso R a b) t
```

```lean
def IsSignedComplexSwap (E F : CochainComplex (ShiftedModuleCategory R) ℤ) (χ : (shiftedTotalTensor R).obj (E, F) ≅ (shiftedTotalTensor R).obj (F, E)) : Prop := letI := monoidalCategory R letI := symmetricCategory R letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R ComplexTensorSwapFormula E F χ
```

```lean
def IsCanonicalDerivedTensorSymmetry (σ : T.tensor ≅ CategoryTheory.Prod.swap _ _ ⋙ T.tensor) : Prop := TensorSymmetryNormalization DerivedCategory.Q (shiftedTensorResolving R) (shiftedTotalTensor R) T.tensor T.representative (IsSignedComplexSwap R) σ
```

```lean
def IsComplexTensorAssociator (E F G : CochainComplex (ShiftedModuleCategory R) ℤ) (χ : (shiftedTotalTensor R).obj ((shiftedTotalTensor R).obj (E, F), G) ≅ (shiftedTotalTensor R).obj (E, (shiftedTotalTensor R).obj (F, G))) : Prop := letI := monoidalCategory R letI := CanonicalTensorPullbackOfUniverses.ringedTensorPreadditive R ComplexTensorAssociatorFormula E F G χ
```

```lean
def IsCanonicalTensorAssociator (α : shiftedTensorLeftTriple R T ≅ shiftedTensorRightTriple R T) : Prop := TensorAssociatorNormalization DerivedCategory.Q (shiftedTensorResolving R) (shiftedTotalTensor R) T.tensor T.representative (IsComplexTensorAssociator R) α
```

```lean
def ShiftedPullbackCoherence (μ : T.tensor ⋙ uStar.mapDerivedCategory ≅ (uStar.mapDerivedCategory.prod uStar.mapDerivedCategory) ⋙ TS.tensor) : Prop := GenericTensorPullbackCoherence T.tensor TS.tensor uStar.mapDerivedCategory (shiftedTensorCanonicalComparison R T) (shiftedTensorCanonicalComparison S TS) (derivedTensorAssociator R T) (derivedTensorSymmetry R T) (derivedTensorAssociator S TS) (derivedTensorSymmetry S TS) μ
```

New public definitions and proved API declarations: `TensorShiftNormalization`, `tensorRightShift`, `tensorLeftShift`, `tensorPairShift`, `totalTensorPairShift`, `GenericTensorPullbackCoherence`, `TensorSymmetryNormalization`, `TensorAssociatorNormalization`, `ResolvingTensorModel`, `ComplexTensorSwapFormula`, `ComplexTensorAssociatorFormula`, `SheafOfModules.shiftedOrdinaryTensor_additive`, `SheafOfModules.shiftedOrdinaryTensor_objAdditive`, `SheafOfModules.shiftedOrdinaryTensor_totalExists`, `SheafOfModules.shiftedTensorComplexComparisonNatIso`.

All helper definitions are actual categorical constructions or complete
equation predicates. No data is chosen from a nonunique unproved existence theorem.

Proof imports added: `KFlatFixedTensorTriangulated` and
`import all DerivedTensorAdditiveConstraints` (both under `Sheaf.Algebra.Homology`).
The latter makes the dependency’s proved private extension lemmas available solely
to theorem proofs. No public definition body refers to a private declaration.
The public imports are unchanged.

## Users

`tools/downstream.py Sheaf.Paper.ShiftedTensorMorphismCalculus --uses` was run for
every changed definition. It lists 118 transitive consumers. Only
`SupportedSourceSystemCupCalculus` uses `shiftedOrdinaryTensor`, and only it and
`SystemPrimitiveComparisonShift` use `ShiftedTensorModel` directly; the other
normalization definitions have no textual external users. Every row below has
the same mathematical statements, with no consumer edit proposed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ShiftedTensorMorphismCalculus | U3 | One original hole closed; equivalent normalization definitions. |
| Sheaf.AlgebraicGeometry.ModuleCupAssociativitySymmetryUnit | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.AlgebraicGeometry.ModuleCupShiftedHomComparison | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.CategoryTheory.InternalBarCharacterRoofCup | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.CategoryTheory.InternalInflationGradedCup | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | R2 | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.AffineCoordinateSupportStalkContinuity | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.AffineSpaceThomMap | B8 | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | F4 | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.CanonicalTateArrowNaturality | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | B7 | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.CartierRelativeBoundaryRealization | H3 | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.CartierRelativeKummerRealization | B8 | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.ConcentratedSupportEtaleTransfer | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCompositor | D8 | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.CoordinateGermCohomologyClasses | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.CoordinateGermConcentrationData | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.CoordinateProductPresentations | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.CoordinateSectionArrows | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.CoordinateSectionProductRecursion | Y8 | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.CoordinateSectionProjection | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | K4 | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.CoordinateZeroBaseChange | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.DivisorNormalizedRealization | E7 | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportCoefficientSquare | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | F1 | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | F3 | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FrameHomZariskiSeparated | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FrameProductElementary | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FrameProductPullback | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FramedEtaleHom | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FramedForgetSupport | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FramedProPredicate | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FramedProRealization | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FramedRealizationAdditive | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FramedRealizationEnlarge | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FramedRealizationIso | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FramedRealizationProperty | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.FramedRealizationPullback | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.KummerProductShearHomotopy | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.KummerProductUnitPermutation | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.LineZeroClassEtaleRealization | B5 | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | W2 | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | S2 | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.PurityDivisorClass | C6 | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | E1 | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.SupportedCupFunctoriality | Q8 | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.SupportedSourceSystemCupCalculus | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Same equations and tensor objects; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Same tensor and resolving comparison fields; constructor syntax checked. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed | Same equations and tensor objects; no adaptation. |

## Status

landed 20261025T164451-L-1021709 2026-10-25 (merge of deliver/U3/Sheaf.Paper.ShiftedTensorMorphismCalculus)
