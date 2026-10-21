# WeilConjectures.compactSupportLevelQuotient

## Reason

The original module defined both the target existence theorem and the coefficient data needed to state its geometric transition lemma. Extract the existing definitions to CompactSupportReductionTowerData to allow that lemma to be stated without an import cycle. The old module publicly imports the data module and retains the coefficient-finiteness unit import explicitly. No existing public signature, data body, attribute or mathematical meaning changes. No WeilConjectures source-library file changes.

## Old

In lean/Sheaf/Paper/CompactSupportReductionTower.lean:

```lean
instance compactSupportLevelFinite (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)

/-- The canonical quotient for any pair of positive coefficient levels.
Source: Stacks Tag 06YY; blueprint proof, step 2
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportLevelQuotient (m n : ℕ) (h : n ≤ m) :
    Padic.coefficientExtensionRing l E (m + 1) →+*
      Padic.coefficientExtensionRing l E (n + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The same quotient after constant sheafification on the small pro-etale site.
Source: Stacks Tag 06YY; blueprint proof, step 2
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportLevelSheafQuotient (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m) :
    integralCoefficientCommRingSheaf l E W m ⟶ integralCoefficientCommRingSheaf l E W n :=
  (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (compactSupportLevelQuotient l E m n h).ulift)

private theorem compactSupportLevelSheafQuotient_self (W : Scheme.{u}) (n : ℕ) :
    compactSupportLevelSheafQuotient l E W n n le_rfl = 𝟙 _ := by
  unfold compactSupportLevelSheafQuotient
  have hq : compactSupportLevelQuotient l E n n le_rfl = RingHom.id _ :=
    Ideal.Quotient.factor_eq
  rw [hq]
  exact (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map_id _

private theorem compactSupportLevelSheafQuotient_step
    (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m) :
    compactSupportLevelSheafQuotient l E W (m + 1) m (Nat.le_succ m) ≫
        compactSupportLevelSheafQuotient l E W m n h =
      compactSupportLevelSheafQuotient l E W (m + 1) n (h.trans (Nat.le_succ m)) := by
  unfold compactSupportLevelSheafQuotient
  rw [← Functor.map_comp]
  congr 1
  ext x
  change (compactSupportLevelQuotient l E m n h)
      ((compactSupportLevelQuotient l E (m + 1) m (Nat.le_succ m)) x.down) =
    (compactSupportLevelQuotient l E (m + 1) n (h.trans (Nat.le_succ m))) x.down
  exact Ideal.Quotient.factor_comp_apply _ _ x.down

/-- Limit projections commute with all coefficient quotients, including m=n.
Source: Stacks Tag 03CO; blueprint proof, steps 1--2
(blueprint: lem-weil-compact-support-reduction-tower-functor).
Proof: for adjacent levels this is the cone compatibility of the completed sheaf.
The quotient factor sends the class of a to the class of a, so successive factors
compose to the direct factor, and the equal-level factor is the identity. Apply
constant sheafification and induct on m-n to obtain compatibility for every pair. -/
theorem compactSupportProjection_comp (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m) :
    completedIntegralCommRingProjectionUnrestricted l E W m ≫
        compactSupportLevelSheafQuotient l E W m n h =
      completedIntegralCommRingProjectionUnrestricted l E W n := by
  induction m, h using Nat.le_induction with
  | base => simp only [compactSupportLevelSheafQuotient_self, Category.comp_id]
  | succ m h ih =>
    rw [← compactSupportLevelSheafQuotient_step l E W m n h, ← Category.assoc]
    have hs : completedIntegralCommRingProjectionUnrestricted l E W (m + 1) ≫
        compactSupportLevelSheafQuotient l E W (m + 1) m (Nat.le_succ m) =
        completedIntegralCommRingProjectionUnrestricted l E W m := by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      apply (forget₂ CommRingCat RingCat).map_injective
      ext x
      have hw := congrArg (fun v ↦ (v.hom.app U).hom x)
        (limit.w (integralCoefficientSheafSystem l E W)
          (homOfLE (Nat.le_succ m)).op)
      simp only [integralCoefficientSheafSystem,
        Functor.ofOpSequence_map_homOfLE_succ] at hw
      convert hw using 1 <;> rfl
    rw [hs]
    exact ih

/-- The canonical composition of exact restrictions along a limit projection and
its quotient, induced by the identity on underlying sections.
Source: Stacks Tag 03DA; blueprint proof, steps 4 and 6
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportRestrictionComp (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m) :
    (proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory ⋙
        scalarReductionDerivedRestriction l E W m ≅
      scalarReductionDerivedRestriction l E W n :=
  pbcDerivedRestrictComp
    (completedIntegralCommRingProjectionUnrestricted l E W m)
    (compactSupportLevelSheafQuotient l E W m n h)
    (completedIntegralCommRingProjectionUnrestricted l E W n)
    (compactSupportProjection_comp l E W m n h)

/-- The quotient-induced derived reduction map. It is the transpose of the
reduction unit under the normalized derived tensor/restriction adjunction.
Thus this is id tensor q on K-flat representatives, rather than an arbitrary map.
Source: Stacks Tags 03CZ and 06YY; blueprint proof, steps 2 and 6
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportReductionMap (W : Scheme.{u}) (m n : ℕ) (h : n ≤ m)
    (K : DerivedCategory (scalarReductionSource l E W)) :
    (scalarReductionDerivedExtension l E W m).obj K ⟶
      ((proEtaleCoefficientRestrictScalars W
        (compactSupportLevelQuotient l E m n h)).mapDerivedCategory).obj
        ((scalarReductionDerivedExtension l E W n).obj K) :=
  (((derivedScalarExtensionRestrictionAdjunction l E W m).choose).homEquiv _ _).symm
    (((derivedScalarExtensionRestrictionAdjunction l E W n).choose).unit.app K ≫
      (compactSupportRestrictionComp l E W m n h).inv.app
        ((scalarReductionDerivedExtension l E W n).obj K))

/-- The specified finite-level composite, including its action on derived morphisms.
Source: Bhatt--Scholze, Definition 6.7.6; blueprint proof, step 4
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportRestrictedLevel {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) :
    DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (scalarReductionSource l E Y) :=
  scalarReductionDerivedExtension l E X n ⋙
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) ⋙
      scalarReductionDerivedRestriction l E Y n

/-- The required transition: quotient-induced reduction, compact support at the
larger level, the specified coefficient comparison, and composition of restrictions.
Source: blueprint proof, step 6; Bhatt--Scholze, Lemma 6.7.7
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportRestrictedTransition {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (m n : ℕ) (h : n ≤ m)
    (K : DerivedCategory (scalarReductionSource l E X)) :
    (compactSupportRestrictedLevel l E c m).obj K ⟶
      (compactSupportRestrictedLevel l E c n).obj K :=
  (scalarReductionDerivedRestriction l E Y m).map
      ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).map
          (compactSupportReductionMap l E X m n h K) ≫
        (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
          ((scalarReductionDerivedExtension l E X n).obj K)) ≫
    (compactSupportRestrictionComp l E Y m n h).hom.app
      ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
        ((scalarReductionDerivedExtension l E X n).obj K))

/-- The canonical constant integral section of the completed coefficient sheaf.
It is obtained from the constant-to-completion map, whose projections are the actual
constant quotient sections. Source: blueprint proof, step 8
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def compactSupportConstantScalar (W : Scheme.{u}) (U : W.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) :
    (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U :=
  ((integralConstantToCompletion l E W).hom.app U)
    (((toSheafify (ProEt.topology W)
      ((Functor.const W.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))).app U)
          (ULift.up a))

/-- Normalization of a linear structure by the actual constant-section action.
Source: blueprint proof, step 8
(blueprint: lem-weil-compact-support-reduction-tower-functor). -/
def IsCompactSupportScalarAction (W : Scheme.{u})
    [Linear (Padic.coefficientExtensionIntegers l E) (scalarReductionSource l E W)] : Prop :=
  ∀ (M N : scalarReductionSource l E W) (v : M ⟶ N)
    (a : Padic.coefficientExtensionIntegers l E) (U : W.ProEtᵒᵖ) (x : M.val.obj U),
    (a • v).val.app U x = compactSupportConstantScalar l E W U a • v.val.app U x
```

## New

The exact block above, verbatim, is in lean/Sheaf/Paper/CompactSupportReductionTowerData.lean. The original module starts with:

```lean
public import Sheaf.Paper.CompactSupportReductionTowerData
```

The original public imports are retained publicly by that data module. The theorem exists_compactSupportReductionTower keeps its signature verbatim and now has an assembled proof. New native evaluation and horizontal transition constructions have their own nodes. No target or definition used by a target changes meaning, so no target-statement re-review is opened by this organizational extraction.

## Users

The table includes the refreshed transitive module list from tools/downstream.py with all ten moved public names passed to --uses, every current textual user found by whole-name search, and the earlier snapshot. The five users reported by the 2026-10-22 server preflight are included. All retain the same exposed declarations and definition bodies. No consumer source is edited.

Current textual users: `Sheaf.Paper.CoefTowerCoaugmentation`, `Sheaf.Paper.CompactSupportNormalizedRealization`, `Sheaf.Paper.CompactSupportReductionTower`, `Sheaf.Paper.CompactSupportReductionTowerConstruction`, `Sheaf.Paper.CompactSupportRepresentativeIndependence`, `Sheaf.Paper.CompactSupportSystemRealizationNormalization`, `Sheaf.Paper.CompactificationCompletedRealization`, `Sheaf.Paper.FiniteTorStability`, `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`, `Sheaf.SixFunctors.CoefTowerEvaluationPairing`, `Sheaf.SixFunctors.CoefTowerNaturalCurrying`, `Sheaf.SixFunctors.FiniteAdjunctionTransition`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactSupportArrowScalarTransport | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactSupportNormalizedRealization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactSupportReductionTower | C4 | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ConstantGeometricStalkUnit | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.DualizingUnitComposite | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.HomFiniteProjective | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.MixedReductionUnit | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.OrientationEtaleCoefficientTwists | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.OrientationEtaleFamily | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.OrientationGeometricComparisons | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PointSectionsCompletionCone | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PointSystemRoosTransport | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PointSystemTransportDescent | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PointTransportConeComparisonDescent | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PointTransportStrictQuotient | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PurityDivisorClass | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PuritySourceTransports | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | A3 | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ResidueControlledFiniteHoms | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SixFunctorDatum | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SixFunctorOrientation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TowerClassChern | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TowerClassFinite | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TowerClassProjective | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TowerClassPullback | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TowerClassReduction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TowerClassSystems | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TowerClassTwisting | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TwConventions | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.WeilInternalHomWeil | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.WfTateTwist | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| TargetsCheck | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| WeilConjectures | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed in local claim snapshot | Same public declarations, signatures and bodies through the data import; no adaptation. |

## Status

landed 20261021T233627-L-839060 2026-10-21 (merge of deliver/C4/Sheaf.Paper.CompactSupportReductionTower)
