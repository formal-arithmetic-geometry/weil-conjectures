# CategoryTheory.filteredHomology_tower_differential

## Reason

The differential module was unclaimed when this repair began. The brief
authorizes restoring an unclaimed dependency with a change record and all users
listed below. Only the assigned main module requires an adapted proof.

The assigned quotient-pages theorem needs the recorded public representative
formula `filteredHomology_tower_differential`. Its declaration was commented out
at synchronization because a private comparison helper moved upstream. Restore
its exact recorded statement as a named remaining theorem so that the completed
quotient comparison proof can use it.

The shared concrete-couple and initial-E definitions remain holed (held by F8),
and the public forward-representative theorem remains commented out (held by A6).
A complete differential proof was checked against an explicit scratch concrete
construction, with only the three allowed axioms. It cannot yet compile against
the published hollow definitions. Neither held module is changed here.

The delivered differential theorem has one `sorry`. This is a decomposition,
not a net hole reduction. No target, definition or existing signature changes.

## Old

The following signature was present only inside a `TAKEN OUT` block comment:

```lean
theorem filteredHomology_tower_differential
    (C : Type u) [Category.{v} C] [Abelian C]
    (hBZ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q r : ℤ) (hr : 1 ≤ r),
      U.obj.filtration.complexBoundaries p (p + q) r ≤
        U.obj.filtration.complexCycles p (p + q) r)
    (eH : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≅
        (U.obj.filtration.gradedPiece p).homology (p + q))
    (hH : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      ∃ (z : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.complexCycles p (p + q) 1 : C))
        (g : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.gradedPiece p).cycles (p + q)),
        z ≫ (U.obj.filtration.complexCycles p (p + q) 1).arrow =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        g ≫ (U.obj.filtration.gradedPiece p).iCycles (p + q) =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        Epi z ∧
        z ≫ cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫
            (eH U p q).hom =
          g ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q))
    (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
    (j : ∀ (s : ℕ) (p q : ℤ),
      (U.obj.filtration.complexCycles p (p + q) (s + 1) : C) ⟶
        (U.obj.filtration.gradedPiece p).cycles (p + q))
    (tQ : ∀ (s : ℕ) (p q : ℤ),
      (U.obj.filtration.complexCycles p (p + q) (s + 1) : C) ⟶
        ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.Z
          s (2 * p + q) (-p) : C))
    (hj : ∀ (s : ℕ) (p q : ℤ),
      j s p q ≫ (U.obj.filtration.gradedPiece p).iCycles (p + q) =
        (U.obj.filtration.complexCycles p (p + q) (s + 1)).arrow)
    (ht : ∀ (s : ℕ) (p q : ℤ),
      tQ s p q ≫
          ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.Z
            s (2 * p + q) (-p)).arrow ≫
          (filteredHomologyEIso U.obj.obj U.obj.filtration p q).hom =
        j s p q ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q))
    (s : ℕ) (p q : ℤ)
    (A : C)
    (a : A ⟶ (U.obj.filtration.step p : CochainComplex C ℤ).X (p + q))
    (a' : A ⟶ (U.obj.filtration.step (p + (s + 1)) :
      CochainComplex C ℤ).X (p + (s + 1) + (q - (s + 1) + 1)))
    (x : A ⟶ (U.obj.filtration.complexCycles p (p + q) (s + 1) : C))
    (y : A ⟶ (U.obj.filtration.complexCycles (p + (s + 1))
      (p + (s + 1) + (q - (s + 1) + 1)) (s + 1) : C))
    (ha : a ≫ (U.obj.filtration.step p).arrow.f (p + q) ≫
      U.obj.obj.d (p + q) (p + (s + 1) + (q - (s + 1) + 1)) =
      a' ≫ (U.obj.filtration.step (p + (s + 1))).arrow.f
        (p + (s + 1) + (q - (s + 1) + 1)))
    (hx : x ≫ (U.obj.filtration.complexCycles p (p + q) (s + 1)).arrow =
      a ≫ (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q))
    (hy : y ≫ (U.obj.filtration.complexCycles (p + (s + 1))
      (p + (s + 1) + (q - (s + 1) + 1)) (s + 1)).arrow =
      a' ≫ (U.obj.filtration.complexQuotientπ (p + (s + 1))
        (p + (s + 1) + 1) (by omega)).f
          (p + (s + 1) + (q - (s + 1) + 1))) :
    x ≫ tQ s p q ≫
        (filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.projection
          s (2 * p + q) (-p) ≫
        ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple s).d
          (2 * p + q) (-p) ≫
        eqToHom (congrArg₂
          ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple s).E
          (show 2 * p + q + 2 + s =
            2 * (p + (s + 1)) + (q - (s + 1) + 1) by omega)
          (show -p - 1 - s = -(p + (s + 1)) by omega)) =
      y ≫ tQ s (p + (s + 1)) (q - (s + 1) + 1) ≫
        (filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.projection
          s (2 * (p + (s + 1)) + (q - (s + 1) + 1)) (-(p + (s + 1)))
```

## New

The same signature is restored as a public theorem with body `:= by sorry`:

```lean
theorem filteredHomology_tower_differential
    (C : Type u) [Category.{v} C] [Abelian C]
    (hBZ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q r : ℤ) (hr : 1 ≤ r),
      U.obj.filtration.complexBoundaries p (p + q) r ≤
        U.obj.filtration.complexCycles p (p + q) r)
    (eH : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≅
        (U.obj.filtration.gradedPiece p).homology (p + q))
    (hH : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      ∃ (z : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.complexCycles p (p + q) 1 : C))
        (g : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.gradedPiece p).cycles (p + q)),
        z ≫ (U.obj.filtration.complexCycles p (p + q) 1).arrow =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        g ≫ (U.obj.filtration.gradedPiece p).iCycles (p + q) =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        Epi z ∧
        z ≫ cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫
            (eH U p q).hom =
          g ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q))
    (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
    (j : ∀ (s : ℕ) (p q : ℤ),
      (U.obj.filtration.complexCycles p (p + q) (s + 1) : C) ⟶
        (U.obj.filtration.gradedPiece p).cycles (p + q))
    (tQ : ∀ (s : ℕ) (p q : ℤ),
      (U.obj.filtration.complexCycles p (p + q) (s + 1) : C) ⟶
        ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.Z
          s (2 * p + q) (-p) : C))
    (hj : ∀ (s : ℕ) (p q : ℤ),
      j s p q ≫ (U.obj.filtration.gradedPiece p).iCycles (p + q) =
        (U.obj.filtration.complexCycles p (p + q) (s + 1)).arrow)
    (ht : ∀ (s : ℕ) (p q : ℤ),
      tQ s p q ≫
          ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.Z
            s (2 * p + q) (-p)).arrow ≫
          (filteredHomologyEIso U.obj.obj U.obj.filtration p q).hom =
        j s p q ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q))
    (s : ℕ) (p q : ℤ)
    (A : C)
    (a : A ⟶ (U.obj.filtration.step p : CochainComplex C ℤ).X (p + q))
    (a' : A ⟶ (U.obj.filtration.step (p + (s + 1)) :
      CochainComplex C ℤ).X (p + (s + 1) + (q - (s + 1) + 1)))
    (x : A ⟶ (U.obj.filtration.complexCycles p (p + q) (s + 1) : C))
    (y : A ⟶ (U.obj.filtration.complexCycles (p + (s + 1))
      (p + (s + 1) + (q - (s + 1) + 1)) (s + 1) : C))
    (ha : a ≫ (U.obj.filtration.step p).arrow.f (p + q) ≫
      U.obj.obj.d (p + q) (p + (s + 1) + (q - (s + 1) + 1)) =
      a' ≫ (U.obj.filtration.step (p + (s + 1))).arrow.f
        (p + (s + 1) + (q - (s + 1) + 1)))
    (hx : x ≫ (U.obj.filtration.complexCycles p (p + q) (s + 1)).arrow =
      a ≫ (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q))
    (hy : y ≫ (U.obj.filtration.complexCycles (p + (s + 1))
      (p + (s + 1) + (q - (s + 1) + 1)) (s + 1)).arrow =
      a' ≫ (U.obj.filtration.complexQuotientπ (p + (s + 1))
        (p + (s + 1) + 1) (by omega)).f
          (p + (s + 1) + (q - (s + 1) + 1))) :
    x ≫ tQ s p q ≫
        (filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.projection
          s (2 * p + q) (-p) ≫
        ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple s).d
          (2 * p + q) (-p) ≫
        eqToHom (congrArg₂
          ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple s).E
          (show 2 * p + q + 2 + s =
            2 * (p + (s + 1)) + (q - (s + 1) + 1) by omega)
          (show -p - 1 - s = -(p + (s + 1)) by omega)) =
      y ≫ tQ s (p + (s + 1)) (q - (s + 1) + 1) ≫
        (filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.projection
          s (2 * (p + (s + 1)) + (q - (s + 1) + 1)) (-(p + (s + 1)))
```

## Users

`tools/downstream.py` was run for this module and theorem. Its textual declaration
search initially found no active use, because the consuming main proof had also been
replaced by `sorry`. The complete transitive downstream list is recorded below.
Adding the previously recorded theorem changes none of these modules' statements
or definitions. Only the assigned main module's proof is adapted in this delivery.
The table records claims observed on 2026-10-18; a holder can finish independently.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FilteredHomologyTowerDifferential | unclaimed | Restore the recorded public theorem as the remaining named obligation. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | X2 | Signature and meaning unchanged; no adaptation required. |
| Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.CategoryTheory.BoundedFilteredComplexPageCore | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.CategoryTheory.BoundedFilteredComplexPages | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.CategoryTheory.BoundedFilteredPageConstruction | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.CategoryTheory.FilteredHomologyCoupleQuotientPages | F7 | Main proof uses the restored representative equation. |
| Sheaf.CategoryTheory.FilteredHomologyTowerQuotients | M6 | Signature and meaning unchanged; no adaptation required. |
| Sheaf.CategoryTheory.FilteredHomotopySpectralSequence | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.CategoryTheory.FilteredQuotientCanonicalStructure | Q1 | Signature and meaning unchanged; no adaptation required. |
| Sheaf.CategoryTheory.FilteredQuotientPageRealization | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedQbarCoefficientConstruction | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedQbarFieldCoefficientSquare | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedQbarFieldEvaluationLinearity | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedQbarFieldFiberExtension | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedQbarFieldPointCoefficientValue | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedQbarScalarPullback | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousChartSchemeNaturality | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousLocallyFreePullback | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.FlatFilteredComplexComparison | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.PoincareDuality.CompatibleIntegralRootBases | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.PoincareDuality.CompatiblePrimitiveRoots | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.PoincareDuality.IntegralResidueLimit | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.PoincareDuality.IntegralResidueQuotient | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.PoincareDuality.IntegralTateBasis | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.PoincareDuality.IntegralTateLocalLine | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.PoincareDuality.TateTwistOneLocalLine | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Signature and meaning unchanged; no adaptation required. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Signature and meaning unchanged; no adaptation required. |
| TargetsCheck | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | B3 | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | B2 | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | Signature and meaning unchanged; no adaptation required. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Signature and meaning unchanged; no adaptation required. |

## Status

landed 20261018T071150-L-1667407 2026-10-18 (merge of deliver/F7/Sheaf.CategoryTheory.FilteredHomologyCoupleQuotientPages)
