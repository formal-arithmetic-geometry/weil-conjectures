# WeilConjectures.coefTowerNaturalCurrying

## Reason

Prune the unused, disputed Lean theorem from the assigned module. Its arbitrary
`eTrace` permits a trace that is not the normalized dualizing counit. The actual
blueprint uses the compatible exceptional counits (current blueprint,
`sec-smooth-purity/sk-lem-sp-tower/prop-coef-integral-dualizing.proof.md`, second
paragraph). The natural-language DAG statement retains that normalization; the
removed Lean formulation did not encode it.

Counterexample: take X to be two disjoint geometric points. At each finite level
B_omega is A_n squared and the canonical trace is the row (1,1). Choose eTrace to
act by the invertible matrix [[1,-1],[0,1]], compatibly at every quotient. The trace
specified by the old ht is then (1,0). Let K be the constant integral module on the
second component, extended by zero. It is constructible of Tor amplitude [0,0]
and X has dimension zero. The specified projection/evaluation pairing has values
in the second summand, hence composition with t is zero. Its curried arrow is zero
between nonzero Hom towers, and cannot be an isomorphism. The same matrix works
in residue characteristic two; it has determinant one over every coefficient ring.
The missing normalization cannot be recovered merely from quotient compatibility.

This theorem already has no Lean consumer and no DAG parent, including proof-step
uses; this was checked against the current server DAG, which includes quarantined
nodes. The unit sk-prop-sf-biduality-general does not list it in realized. The
current route already uses integralDualizing_mapping_tower_finite_comparison
(node lem-coef-integral-dualizing-mapping-tower-finite-comparison), whose proof
constructs the coherent trace from the actual finite exceptional counits and
explicitly avoids this arbitrary-trace claim. This delivery does not replace that
existing proof obligation or remove it. No parent dependency edits are needed.

Retain this nonempty module because four direct importers use its definitions.
Every definition, instance, signature, attribute and public import is preserved.
Only the false theorem and six unused proof imports are removed. The model
structure docstring is corrected to describe a data interface without referring
to the withdrawn existence claim. No target statement or definition used by a
target changes, so this does not reopen target-statement review.

## Old

The removed declaration's signature, verbatim:

```lean
theorem coefTowerNaturalCurrying (hl : l ≠ D.p)
    (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n)
    (_hQ : ∀ {m n : ℕ} (h : n ≤ m),
      (coefficientSequenceDerivedTransition.{u, u} l E X h).app (coefTraceInput l E X Q) ≫
          (normalizedDVRRes.{u, u} l E X h).map (eQ n).hom =
        (eQ m).hom ≫ integralDualizingExceptionalTransition l E D X hl h)
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (a₀ b₀ : ℤ) (_hab : a₀ ≤ b₀)
    (T : DerivedCategory (scalarReductionSource.{u, u} l E X) ⥤
      DerivedCategory (pbcTowers (Spec (.of D.k))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))))
    (e : ∀ n : ℕ, T ⋙ pbcTowerEvaluation (Spec (.of D.k))
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) n ≅
        compactSupportRestrictedLevel l E (finiteDualizingCompactification D X) n)
    (_htransition : ∀ (m n : ℕ) (h : n ≤ m)
      (K : DerivedCategory (scalarReductionSource.{u, u} l E X)),
      (pbcTowerTransition (Spec (.of D.k))
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))) m n h).app
          (T.obj K) ≫ (e n).hom.app K =
        (e m).hom.app K ≫ compactSupportRestrictedTransition l E
          (finiteDualizingCompactification D X) m n h K)
    (eTrace : ∀ n : ℕ,
      (coefTraceEvaluation l E n).obj (coefTraceDualizingTower l E D X Q) ≅
        coefTraceFiniteValue l E D X n)
    (t : coefTraceDualizingTower l E D X Q ⟶ coefCurryingTarget l E)
    (_ht : ∀ n : ℕ,
      (coefTraceEvaluation l E n).map t ≫ (coefCurryingTargetEvaluation l E n).hom =
        (eTrace n).hom ≫ coefTraceFiniteCounit l E D X n ≫
          (coefTraceTargetIso l E D n).hom) :
    ∃ M : CoefCurryingModels l E D X Q a₀ b₀ T e,
      M.IsSpecified l E D X Q a₀ b₀ T e ∧
      (∀ (C : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)))
        (P : CochainComplex (ModuleCat.{u + 1} (coefTraceRing l E)) ℤ)
        (_hP : (HomologicalComplex.quasiIso
          (ModuleCat.{u + 1} (coefTraceRing l E)) (.up ℤ)).kFlat P)
        (_eP : DerivedCategory.Q.obj P ≅ C)
        (I : CochainComplex (coefPairingModules l E) ℤ)
        (_hI : I.IsKInjective) (_eI : DerivedCategory.Q.obj I ≅ coefCurryingTarget l E),
        Nonempty ((M.hom.hom).obj (op C) ≅
          DerivedCategory.Q.obj (coefCurryingHomComplex l E P I))) ∧
      (∀ (C : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))) (n : ℕ),
        (coefTraceEvaluation l E n).map (M.hom.evaluation C) ≫
            (coefCurryingTargetEvaluation l E n).hom =
          (M.tensorEvaluation n).hom.app
              ((M.hom.hom).obj (op C),
                (CoefTower.constant (coefTraceRing l E)).obj C) ≫
            ((M.homEvaluation n).hom.app (op C) ⊗ₘ
              (CoefTower.constantEvaluation (coefTraceRing l E) n).hom.app C) ≫
                coefCurryingPointEvaluation l E n C) ∧
      (∀ (K : (CoefTower.inputs l E (X := X) a₀ b₀).FullSubcategory) (n : ℕ),
        (coefTraceEvaluation l E n).map ((M.eta l E D X Q a₀ b₀ T e).app K) ≫
            (M.supportEvaluation l E D X Q a₀ b₀ T e n).hom.app K.obj =
          (CoefTower.constantEvaluation (coefTraceRing l E) n).hom.app
              ((coefCurryingIntegralSections l E D X T).obj K.obj) ≫
            M.finiteProjection l E D X Q a₀ b₀ T e n K) ∧
      (∀ n : ℕ, (M.omegaEvaluation n).hom ≫ (M.omegaOrigin n).hom = (eTrace n).hom) ∧
      (∀ K : (CoefTower.inputs l E (X := X) a₀ b₀).FullSubcategory,
        IsIso (M.gamma l E D X Q a₀ b₀ T e t K)) ∧
      (∀ (K : (CoefTower.inputs l E (X := X) a₀ b₀).FullSubcategory) (n : ℕ),
        (coefTraceEvaluation l E n).map (M.gamma l E D X Q a₀ b₀ T e t K) ≫
            (M.homEvaluation n).hom.app
              (op ((coefCurryingIntegralSections l E D X T).obj K.obj)) =
          (M.finiteHom n).hom.app (op K.obj) ≫
            M.finiteArrow l E D X Q a₀ b₀ T e n K) ∧
      ∀ (K K' : (CoefTower.inputs l E (X := X) a₀ b₀).FullSubcategory) (f : K ⟶ K'),
        M.gamma l E D X Q a₀ b₀ T e t K' ≫
            (M.hom.hom).map ((coefCurryingIntegralSections l E D X T).map f.hom).op =
          (coefPairingHom l E X M.calculus Q).map f.hom.op ≫
            M.gamma l E D X Q a₀ b₀ T e t K
```

Its entire proof was `by sorry`.

## New

The declaration WeilConjectures.coefTowerNaturalCurrying is removed without a
replacement declaration. Its node's lean field is explicitly null; the original
mathematical statement and proof plan remain in the DAG, currently unreached.
All 27 surviving declarations retain their original bodies and signatures. Their
Lean attachments are preserved by the two existing definition nodes:
def-coef-integral-dualizing-quotient-tower records the quotient tower, target and
target evaluation; def-coef-tower-currying-models records the other constructions.

Removed proof-only imports:

- Sheaf.CategoryTheory.SequentialTowerEvaluationFull
- Sheaf.CategoryTheory.DiagramSiteRealization
- Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
- WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
- Mathlib.CategoryTheory.Abelian.FunctorCategory
- Sheaf.Algebra.Homology.ScalarInternalHomAdjunction

The returned delivery 61f1083f956 passed mathematical review (C-61f10) but the
landing source census reported <unattributed:41:1833>. Reproducing that census
located the marker in `set_option warn.sorry false`, not in a declaration body.
Remove that unused option: the module has no proof holes for it to suppress.
The same source census now reports no hole rows or warnings, and missing_gate
against current server main reports no failures. This changes no declaration,
instance, attribute, definition body or public import from the reviewed delivery.
The node edits have been reapplied only to the lean fields of current server
records, retaining all current metadata. The delivery tool builds on current
sheaf-dag automatically.

## Users

Current server source-closure inventory (2026-10-28); this table includes all
transitive importers, although none mentions the removed theorem. The four direct
importers are compiled against the changed module. No consumer is adapted.
Public imports and all surviving construction interfaces are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.DeligneLaumon.MarkedGeometricCurveModel | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicActualSystemsNormalized | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicNormalizedPuritySystems | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicPuritySourceNormalization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicPuritySourceTransitionSquare | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AffineSpaceProductDomain | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.CochainLocalizationTensorIso | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationCore | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationShift | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionCoherenceLaws | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFieldStages | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionIntegralStages | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.DerivedWeilOperations | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FieldOrientedExchangeSquares | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FieldProjectionRefinementSquare | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteDiagonalDncReduction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteFirstRootChart | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteIntrinsicProjectionCompatibility | C3 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteIntrinsicProjectionRealization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FinitePositiveChartFrameExt | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FinitePositiveChartRecursion | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FinitePositiveRootChartPower | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FinitePositiveRootCharts | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteProjectionExchangeData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteProjectionIdentityNormalization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteProjectionOpenAssembly | D5 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteProjectionOperationPresentation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteProjectionRefinementLeft | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteProjectionTensorSquare | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FinitePurityCounitSystem | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteReductionBaseChangeSource | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteReductionExceptionalFiniteModel | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteReductionLineChartScalars | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteReductionLineInputConstructible | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteReductionReassociation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteReductionShiftedPullbackCube | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorFactors | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorSource | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteReductionThetaFactor | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteRestrictionDiagramNaturality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteScalarCochainComparisonIso | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteScalarMonoidalRepresentative | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteScalarRepresentativeIso | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteScalarTensorData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteScalarTensorSource | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteSignedTwistProducts | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteSupportedReductionEquation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTateSourceMap | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTateSourceStructuralCoherence | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTensorComparisonEquations | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTensorLineChartReduction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTensorLineDerivedExistence | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTensorLineDerivedExistenceWitness | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTensorPresentationReduction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTensorProductFrameExt | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTensorProductMap | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTensorProductMapIsIso | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTensorPullbackCompositionReduction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTensorPullbackTensorReduction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTensorSemilinearReduction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftCoherence | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftFirst | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftSecond | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTensorSignedReduction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FixedPresentationUniformizerReductions | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FrobeniusCompactIntegralAmbientNormalization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FrobeniusCompactIntegralNormalization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.FrobeniusCompactRationalNormalization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.GeometricSmoothReconstructionSetup | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IntegralDualizingExceptionalUnit | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IntegralEquivarianceMate | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IntegralEquivarianceNaturality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IntegralGeometricComparisonData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IntegralGeometricComparisonRealization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IntegralGeometricPurityRealization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IntegralGeometricReindexingRealization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IntegralGeometricSupportRealization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IntegralGeometricTransposeIdentity | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IntegralOrientedExchangeSquares | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IntegralProjectionFiniteEvaluation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IntegralProjectionReductionCoordinates | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IntegralProjectionSystemEvaluation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IntegralPurityCounitReduction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IntegralStageProjectionReduction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IntegralStageProjectionStructuralIdentities | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IteratedPurityScalarPasting | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.IteratedTateSourceComposite | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.NativeWeilDualizingHomTransposition | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTrace | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.NormalizedIntegralTraceData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.NormalizedSmoothOrientationUnits | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.NormalizedSupportEtalePresentation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.PoincareDualityConventions | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.ProjectionFiniteBaseChangeDiamondEquality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteCalculation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteExpansion | D6 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.ProjectionFiniteBaseChangeRightLeftPath | D7 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.ProjectionFiniteBaseChangeRightRouteCalculation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.ProjectionFiniteBaseChangeRouteRealization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.ProjectionFiniteBaseChangeTransport | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.ProjectionIdentityAssembly | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.PurityCompactSupportTransport | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.PurityFiniteTateSourceComparisonCalculus | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.PurityKappaStages | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.PurityTateDatum | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RationalPurityExchangeEndpointData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RationalPurityExchangeEndpoints | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RationalPurityLocalizedFamilyData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RationalizationOrientedExchangeSquare | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.ScalarHomPresentationEvaluation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SmoothExchangeScalarCompatibility | C4 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SmoothOrientationCoefficientFamily | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SmoothOrientationPuritySquares | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SmoothOrientationStageExchange | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SmoothOrientedExchangeComparisons | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SpecifiedIntegralUnitOrientation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SystemScalarBasisDistributivity | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SystemScalarRefinementRestriction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.SystemScalarTensorConstituents | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TensorHomExchange | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TowerTraceCanonicalIntegral | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TowerTraceNormalizedPresentations | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TowerTraceOrientationUniqueness | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TowerTracePurityComparison | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TowerTracePurityComparisonData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TowerTraceScalarCounit | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TransportIntegralCounitRealization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.VerdierHomChainCompositionData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.VerdierIdentityProjection | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.WeilEquivarianceOfPurityAndTrace | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.Paper.WeilPurityEquivarianceData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | V4 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient | B7 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteDualizingCoherence | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionBetaReductionSquare | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionCocycles | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionComposition | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionDeltaSquare | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionHomMapInvertibility | W3 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionHomReductionSquare | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionIdentityE | S1 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionIdentityL | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibilityTriangulated | T1 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionPureTensor | W4 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionReductionPairing | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionTranspose | X2 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionUInvertibility | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionUReconstruction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionUReductionIsInvertible | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionVInvertibility | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralScalarQuotientTransition | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralScalarQuotientTransitionTranspose | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralScalarQuotientTransitionTransposeCore | C8 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarFiniteExceptionalCore | X3 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarFiniteExceptionalFormula | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarFiniteExceptionalScalar | T2 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarFiniteOmegaStageCoherence | T4 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarFiniteScalarCocycles | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarRationalScalarCocycles | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierBiduality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierBidualityDescent | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierComparison | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierCore | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierCoreEquations | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierDualInclusion | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierDualizing | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierEvaluationDescent | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierEvaluationRepresentatives | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierExactness | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierExceptional | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierFiniteCoherence | N2 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierFiniteEvaluationScalar | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierFiniteEvaluationStage | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierFunctor | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierHomComparisonComponents | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierHomComparisonExtension | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierHomComparisonScalarPasting | Y2 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierInternalHom | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierInternalHomComparison | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierInternalHomUniversal | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierScalars | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierShift | Y3 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierTensorDescent | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierTensorInclusion | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefScalarReductionExchange | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefWeilExceptionalCompatibility | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefWeilLeftExchangeCompatibility | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefWeilNormalizedDuality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefficientSystemSymmetricCalculus | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefficientUnitFiniteTor | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CoefficientUnitNormalization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.CompletedSystemPullbackPreservation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionCoefficientUnitData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionGeometricRealization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemDuality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemEnriched | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Direct importer; construction API unchanged; no theorem use. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | unclaimed | Direct importer; construction API unchanged; no theorem use. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptionalData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptionalQuotientCoherence | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptionalQuotientIso | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicBidualComparison | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicTensorRealization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicTensorSymmetry | A7 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizingCoefficientHomTowerLimit | A8 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizingExceptionalUnitBridge | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizingMappingLimit | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizingMappingLimitGlobal | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizingMappingTower | unclaimed | Direct importer; construction API unchanged; no theorem use. |
| Sheaf.SixFunctors.IntegralDualizingMappingTowerFiniteComparison | A9 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizingMappingTowerLimit | B5 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalLimitConstructible | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralSupportRealizationComparison | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemDualityCompatibility | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierModels | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairing | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairingDelta | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairingDeltaUncurried | B6 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairingTransition | U1 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierSignedCalculus | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.KappaCoefficientCoherence | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.KappaGeometricComparisons | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.KappaMixedCoherence | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Direct importer; construction API unchanged; no theorem use. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarPreparation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarSupportCompatibility | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalDualFormulaAdjunction | U2 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalDualFormulaScalarCounit | P1 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalDualizingIdentification | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalExceptionalIdentifications | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalHomAdjunction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalHomIdentifications | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalHomScalarCounitNormalization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalHomScalarEvaluation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalHomScalarEvaluationCore | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalOperationsData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierComparisonBiduality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierComparisonEvaluation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierComparisonEvaluationIntegral | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierComparisonNaturality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierCompletion | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierComposition | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierCompositionEquation | Q1 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierCompositionNormalization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierDatum | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierDatumFromIntegral | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierDatumNaturality | B2 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierEvaluationDetection | B8 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierExtension | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierIntegralBetaNaturality | U3 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierIntegralCocycle | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierIntegralCompNormalization | U4 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierLocalizedCore | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierLocalizedEvaluation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierLocalizedExact | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierModels | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierPairingCalculus | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierScalarInterchange | V1 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierSignedKFlat | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierUnit | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.SystemTotalEnrichedTranspose | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.WeilSheaf.CoefficientCohomologyComparison | F4 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.WeilSheaf.SmoothCoefficientVanishing | K2 | Indirect importer; no theorem use; no adaptation. |
| Sheaf.WeilSheaf.SmoothDualizingCohomology | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.WeilSheaf.SmoothDualizingConcentration | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.WeilSheaf.SmoothDualizingVanishing | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.WeilSheaf.StructuralBidualInvertible | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.WeilSheaf.StructuralDualizingIdentification | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.WeilSheaf.StructuralOmegaHomPairs | unclaimed | Indirect importer; no theorem use; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Indirect importer; no theorem use; no adaptation. |
| TargetsCheck | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.Statement | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.WeilSheaf.Karoubian | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.WeilSheaf.KaroubianPointer | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Indirect importer; no theorem use; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Indirect importer; no theorem use; no adaptation. |

## Status

landed 20261028T055621-L-777591 2026-10-28 (merge of deliver/C2/Sheaf.SixFunctors.CoefTowerNaturalCurrying)
