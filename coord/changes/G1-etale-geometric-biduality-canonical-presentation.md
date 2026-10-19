# WeilConjectures.FiniteEtaleGeometricBiduality

## Reason

The original proposition extracts the normalized evaluation transpose through three nested
existential choices in AmbientDualityPairing. Specializing the normalization equality to
etale module sheaves repeatedly exceeds the 60-second file limit. Abstract normalization
and Koszul symmetry calculations compile, but concrete instance expansion dominates the
bridge. Naming the existing source canonical transformation gives the same arrow directly.
The four categorical clauses are factored through GeometricBidualityConclusion to prevent
repeated unfolding of the concrete derived category during kernel checking. No limit is
raised and no file is split to avoid the limit. The repaired complete item compiles in 9 s.

Equality of the mathematical maps: the old witness fixes b to the descended Koszul braiding.
Its evaluation e satisfies curry(b(K,DK) followed by e)=id, hence, by the tensor-Hom
bijection, b(K,DK) followed by e=ev(K). The symmetry identity makes
b(K,DK) inverse equal b(DK,K), so e=b(DK,K) followed by ev(K). Its chosen delta is curry(e),
which is exactly MonoidalClosed.toIhomIhom and therefore verdierDualDoubleDual.app. This
works for every ambient object and every pairing witness. The source braiding is the same
signed interchange (the two Koszul signs multiply to one) descended through localization.
Thus replacing the witness-extracted map by this source construction preserves the full
assertion, not merely the existence of some double-dual isomorphism. Keeping the pairing
witness as a conjunction is equivalent to the previous existential over its proof because
the remaining clauses now refer to its uniquely specified canonical map.

The generic definition merely factors the identical invertibility, preservation, functor
comparison, and explicit triangle formula; it does not assert them. It has no proof fields
filled by sorry and chooses no data. Edge cases: the zero object and empty scheme are
included; n remains positive; no assumption of regularity, smoothness, or properness is
introduced. The original theorem's binders, universes, visibility and conclusion text stay
unchanged. No Challenge declaration or definition used in a Challenge signature changes;
none of those signatures mentions this proposition. The finite-stage parent and the
proposition's normalization are submitted for independent statement review with this record.

## Old

```lean
noncomputable def FiniteEtaleGeometricBiduality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {k : Type u} [Field k] (X : Scheme.{u}) (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] : Prop :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  ∃ h : Etale.AmbientDualityPairing
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X
      (Etale.dualizingComplex
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) aX),
    (∀ K : Etale.DerivedCategoryModule
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X,
      finiteTorConstructibleEtale l E n hn X K →
        IsIso (Etale.AmbientDualityPairing.bidualityMap
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X h K)) ∧
    (∀ K : Etale.DerivedCategoryModule
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X,
      finiteTorConstructibleEtale l E n hn X K →
        finiteTorConstructibleEtale l E n hn X
          ((Etale.verdierDual
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) aX).obj
              (op K))) ∧
    (∃ e : (finiteTorConstructibleEtale l E n hn X).FullSubcategoryᵒᵖ ≌
        (finiteTorConstructibleEtale l E n hn X).FullSubcategory,
      Nonempty (e.functor ⋙ (finiteTorConstructibleEtale l E n hn X).ι ≅
        (finiteTorConstructibleEtale l E n hn X).ι.op ⋙ Etale.verdierDual
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) aX)) ∧
    ∃ s : (Etale.verdierDual
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) aX).CommShift
        ℤ,
      ∀ T : Triangle (Etale.DerivedCategoryModule
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X)ᵒᵖ,
        finiteTorConstructibleEtale l E n hn X T.obj₁.unop →
        finiteTorConstructibleEtale l E n hn X T.obj₂.unop →
        finiteTorConstructibleEtale l E n hn X T.obj₃.unop →
        T ∈ distTriang (Etale.DerivedCategoryModule
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X)ᵒᵖ →
        Triangle.mk
          ((Etale.verdierDual
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) aX).map
              T.mor₁)
          ((Etale.verdierDual
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) aX).map
              T.mor₂)
          ((Etale.verdierDual
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) aX).map
              T.mor₃ ≫ (s.commShiftIso (1 : ℤ)).hom.app T.obj₁) ∈
          distTriang (Etale.DerivedCategoryModule
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X)
```

## New

```lean
def GeometricBidualityConclusion
    {C : Type*} [Category C] [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) (V : Cᵒᵖ ⥤ C) (δ : 𝟭 C ⟶ V.rightOp ⋙ V) : Prop :=
  (∀ K, P K → IsIso (δ.app K)) ∧
  (∀ K, P K → P (V.obj (op K))) ∧
  (∃ e : P.FullSubcategoryᵒᵖ ≌ P.FullSubcategory,
    Nonempty (e.functor ⋙ P.ι ≅ P.ι.op ⋙ V)) ∧
  ∃ s : V.CommShift ℤ,
    ∀ T : Triangle Cᵒᵖ, P T.obj₁.unop → P T.obj₂.unop → P T.obj₃.unop →
      T ∈ distTriang Cᵒᵖ →
      Triangle.mk (V.map T.mor₁) (V.map T.mor₂)
        (V.map T.mor₃ ≫ (s.commShiftIso (1 : ℤ)).hom.app T.obj₁) ∈ distTriang C

noncomputable def FiniteEtaleGeometricBiduality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {k : Type u} [Field k] (X : Scheme.{u}) (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] : Prop :=
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  Etale.AmbientDualityPairing
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X
      (Etale.dualizingComplex
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) aX) ∧
    GeometricBidualityConclusion (finiteTorConstructibleEtale l E n hn X)
      (Etale.verdierDual
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) aX)
      (Etale.verdierDualDoubleDual
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) aX)
```

## Users

The required downstream.py scan reports 467 transitive importers and exactly two textual
users, including the item itself. Every listed module is accounted for below. The sole
other textual user was compiled unchanged against the repaired item. Since none of the
remaining modules mentions the definition, there is no projection, destructuring proof,
or construction to adapt in them. Public imports are retained, so visibility is unchanged.
No module held by another group is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.EtaleGeometricBiduality | G1 | Same mathematical proposition; canonical presentation and completed proof. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.DeligneLaumon.GenericDualityModel | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalBase | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalCoherence | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalComposition | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalOperations | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjection | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalProjectionData | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.AdicExceptionalScalars | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CommonAdicSectionData | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.DualStalkFrobenius | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteRegularReductionDualizing | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | not adapted; ownership immaterial | Only other textual user. It asserts a conjunction with this same biduality proposition; unchanged source compiles against the repair (7.6 s). No adaptation. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.InternalHomPullback | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBound | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.PurityChernClasses | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.RationalStalkExact | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.SystemClopenTensorCompatibility | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TowerClassChern | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TowerClassCoefficients | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TowerClassDiagonal | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TowerClassFinite | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TowerClassProjective | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TowerClassPullback | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TowerClassReduction | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TowerClassSystems | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TowerClassTwisting | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TwConventions | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TwFrobeniusAction | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.WeilOne | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Targets.PoincareUncurry | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| TargetsCheck | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.Statement | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyZero | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | not adapted; ownership immaterial | Transitive importer only; no occurrence of the changed definition. Existing declarations and meanings unchanged; no adaptation. |

## Status

landed 20261019T192731-L-1860863 2026-10-19 (merge of deliver/G1/Sheaf.Paper.EtaleGeometricBiduality)
