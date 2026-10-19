# CategoryTheory.multivariableDerivedCalculus private product helpers

## Reason

The proof needs private finite-product connectedness and product-square equivalence helpers.
Their shared binders are declared in a new `section PiSquares`, closed before either existing
public theorem. The static interface check conservatively flags these `variable` commands.
This record documents their scope. All helpers are fully proved and private; no public
declaration signature, visibility, definition, import or target meaning changes.
No consumer requires adaptation.

## Old

```lean
open _root_.CategoryTheory.Functor

variable (n : ℕ) (A : Fin n → Type uA) (P : Fin n → Type uP) (D : Fin n → Type uD)
  [∀ i, Category.{vA} (A i)] [∀ i, Category.{vP} (P i)] [∀ i, Category.{vD} (D i)]
  (I : ∀ i, P i ⥤ A i) [∀ i, (I i).Full] [∀ i, (I i).Faithful]
  (W : ∀ i, MorphismProperty (A i)) (L : ∀ i, A i ⥤ D i)
  [∀ i, (W i).ContainsIdentities] [∀ i, (L i).IsLocalization (W i)]
  {H : Type uH} [Category.{vH} H]
```

## New

```lean
open _root_.CategoryTheory.Functor

section PiSquares

variable {J : Type} {C₁ : J → Type uA} {C₂ : J → Type uP}
  {C₃ : J → Type uD} {C₄ : J → Type uH}
  [∀ j, Category.{vA} (C₁ j)] [∀ j, Category.{vP} (C₂ j)]
  [∀ j, Category.{vD} (C₃ j)] [∀ j, Category.{vH} (C₄ j)]
  {T : ∀ j, C₁ j ⥤ C₂ j} {L₀ : ∀ j, C₁ j ⥤ C₃ j}
  {R : ∀ j, C₂ j ⥤ C₄ j} {B : ∀ j, C₃ j ⥤ C₄ j}
  (w : ∀ j, TwoSquare (T j) (L₀ j) (R j) (B j))

private abbrev piSquare : TwoSquare (Functor.pi T) (Functor.pi L₀)
    (Functor.pi R) (Functor.pi B) := NatTrans.pi w

variable {X₂ : ∀ j, C₂ j} {X₃ : ∀ j, C₃ j}
  (g : (Functor.pi R).obj X₂ ⟶ (Functor.pi B).obj X₃)

set_option backward.isDefEq.respectTransparency false in
private def piTriplesTo :
    (piSquare w).StructuredArrowRightwards g ⥤
      ∀ j, (w j).StructuredArrowRightwards (g j) where
  obj X j := TwoSquare.StructuredArrowRightwards.mk (w j) (g j)
    (X.right.left j) (X.hom.left j) (X.right.hom j) (by
      have h := congrFun X.hom.w j
      dsimp [TwoSquare.costructuredArrowRightwards, piSquare,
        Comma.mapLeft, CostructuredArrow.post] at h ⊢
      change (R j).map _ ≫ (w j).app _ ≫ (B j).map _ = g j
      simpa [Functor.pi, NatTrans.pi] using h)
  map {X Y} f j := StructuredArrow.homMk
    (CostructuredArrow.homMk (f.right.left j) (by
      exact congrFun (CostructuredArrow.w f.right) j)) (by
        ext
        have eq := congrArg (fun k ↦ k.left j) (StructuredArrow.w f)
        dsimp at eq ⊢
        exact eq)
  map_id _ := rfl
  map_comp _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
private def piTriplesFrom :
    (∀ j, (w j).StructuredArrowRightwards (g j)) ⥤
      (piSquare w).StructuredArrowRightwards g where
  obj X := TwoSquare.StructuredArrowRightwards.mk _ _ (fun j ↦ (X j).right.left)
    (fun j ↦ (X j).hom.left) (fun j ↦ (X j).right.hom) (by
      funext j
      have h := (X j).hom.w
      dsimp [TwoSquare.costructuredArrowRightwards, piSquare,
        Comma.mapLeft, CostructuredArrow.post] at h ⊢
      change (R j).map _ ≫ (w j).app _ ≫ (B j).map _ = g j
      simpa [Functor.pi, NatTrans.pi] using h)
  map {X Y} f := StructuredArrow.homMk
    (CostructuredArrow.homMk (fun j ↦ (f j).right.left) (by
      funext j
      exact CostructuredArrow.w (f j).right)) (by
        ext j
        have eq := congrArg (fun k ↦ k.left) (StructuredArrow.w (f j))
        dsimp at eq ⊢
        exact eq)
  map_id _ := rfl
  map_comp _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
private def piTriplesEquivalence :
    (piSquare w).StructuredArrowRightwards g ≌
      ∀ j, (w j).StructuredArrowRightwards (g j) where
  functor := piTriplesTo w g
  inverse := piTriplesFrom w g
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp X := by
    ext j
    simp [piTriplesTo, piTriplesFrom]

private theorem piSquareExact [Finite J] [∀ j, (w j).GuitartExact] :
    (piSquare w).GuitartExact := by
  rw [TwoSquare.guitartExact_iff_isConnected_rightwards]
  intro X₂ X₃ g
  have : ∀ j, IsConnected ((w j).StructuredArrowRightwards (g j)) :=
    fun j ↦ TwoSquare.GuitartExact.isConnected_rightwards (w := w j) (g j)
  have := finitePiConnected (fun j ↦ (w j).StructuredArrowRightwards (g j))
  exact isConnected_of_equivalent (piTriplesEquivalence w g).symm

end PiSquares

variable (n : ℕ) (A : Fin n → Type uA) (P : Fin n → Type uP) (D : Fin n → Type uD)
  [∀ i, Category.{vA} (A i)] [∀ i, Category.{vP} (P i)] [∀ i, Category.{vD} (D i)]
  (I : ∀ i, P i ⥤ A i) [∀ i, (I i).Full] [∀ i, (I i).Faithful]
  (W : ∀ i, MorphismProperty (A i)) (L : ∀ i, A i ⥤ D i)
  [∀ i, (W i).ContainsIdentities] [∀ i, (L i).IsLocalization (W i)]
  {H : Type uH} [Category.{vH} H]
```

## Users

The downstream import closure has 241 modules, listed below. Source searches
for both public theorem names found no external calls. The direct importer is
`Sheaf.SixFunctors.IntTensorProjection`; it only imports the module. Private helper names
cannot affect any consumer. This delivery changes no consumer and no target definition.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.CompactificationLocalizing | F4 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | V5 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | Y8 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.FiniteProperLocalizing | V9 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.FiniteTorStability | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.IntegralExtensionByZero | A3 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.InterchangeProperPasting | S4 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | J5 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.MateOpenRestriction | D7 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.OpenImmersionLocalizing | X5 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.ProperHeartBound | K5 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.ProperHeartBoundLattice | G2 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.ProperHeartBoundTorsion | J4 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.ProperUnboundedWindowIso | F8 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.RestrictionLocal | R3 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.SfBidualityClass | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.SmoothTrace | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.UnboundedBaseChangeExtension | K3 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.VerdierExchange | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.WeilOne | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.FieldTensor | N1 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.IntTensorProjection | G4 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | T4 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | B4 | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Targets.PoincareUncurry | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | No effect: section-local binders; public signatures unchanged. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No effect: section-local binders; public signatures unchanged. |
| TargetsCheck | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.Statement | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.TraceFormula.Statement | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No effect: section-local binders; public signatures unchanged. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No effect: section-local binders; public signatures unchanged. |

## Status

landed 20261019T005355-L-2760207 2026-10-19 (merge of deliver/P2/Sheaf.CategoryTheory.MultivariableDerivedCalculus)
