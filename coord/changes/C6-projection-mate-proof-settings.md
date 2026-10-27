# SheafOfModules.RingedTensorCorner.mateTensor

## Reason

The original proof repeatedly unfolded large tensor-descent and total-complex records.
The assigned theorem is proved by comparing its recorded tensor model with the published
independent-coefficient tensor and transporting canonical shifts, exactness and units.
The definition repairs below preserve the objects and propositions by definitional equality.
The theorem signature is byte-identical to the current library signature. No Challenge target,
source-library declaration, axiom, or proof hole is added or changed.

The item adds public names for the source and target of its existing representative comparison,
the comparison itself and its component equality, and generic forms of the two existing
normalization predicates. Their data and conditions are the original ones. The native cochain
unit is definitionally the old degree-zero ring complex, and the ordinary tensor is the existing
KFlatFixedTensor ordinary tensor, definitionally the old curried tensor.

KFlatFixedTensor.derivedTensor now refers directly to the published independent-coefficient
tensor rather than projecting that same functor out of selectedTensorPresentation. The
representative presentation and all its data remain unchanged. Its equality proof is now rfl
after unfolding derivedTensor; selectedTensorPresentation is made semireducible only locally
for the following existing proofs.

The unclaimed PullbackTensorCanonicalShiftUnit module adds the proved public theorem
canonicalRepresentativeIso_naturality, an API wrapper for its existing private joint naturality
lemma. No existing declaration, proof or visibility changes there. It lets the item construct
the representative model directly from the existing comparison components.

File-local elaboration settings and irreducibility attributes keep these interfaces folded.
The two cochain monoidal instances are disabled only inside the item's section. All additional
instances used to choose the existing KFlatFixedTensor proof instances are local; no global
instance is registered. Scoped heartbeat settings control elaboration only; every file still
has the unchanged 60-second compile limit. All private helpers are fully proved.

## Old

```lean
noncomputable abbrev RingedTensorCorner.mateUnitComplex (A : RingedTensorCorner.{u, w}) :=
  (CochainComplex.singleFunctor A.mateModules 0).obj
    (SheafOfModules.unit ((sheafCompose A.topology
      (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring))

noncomputable abbrev RingedTensorCorner.mateTensor (A : RingedTensorCorner.{u, w}) :=
  @MonoidalCategory.curriedTensor A.mateModules _ (monoidalCategory A.ring)

def RingedTensorModel.MateCanonicalShifts {A : RingedTensorCorner.{u, w}}
    (a : RingedTensorModel A) [(Functor.curryObj A.tensor).CommShift₂Int] : Prop :=
  letI := monoidalCategory A.ring
  letI := ringedTensorPreadditive A.ring
  (∀ (P : CochainComplex A.mateModules ℤ) (n : ℤ), A.mateFlat P → A.mateFlat (P⟦n⟧)) ∧
  (∀ (P Q : CochainComplex A.mateModules ℤ) (hP : A.mateFlat P) (hQ : A.mateFlat Q)
      (n : ℤ) (hPn : A.mateFlat (P⟦n⟧)),
    a.representative.hom.app (⟨P⟦n⟧, hPn⟩, ⟨Q, hQ⟩) ≫
        A.tensor.map (Prod.mkHom ((DerivedCategory.Q.commShiftIso n).hom.app P)
          (𝟙 (DerivedCategory.Q.obj Q))) ≫
        (((Functor.curryObj A.tensor).flip.obj (DerivedCategory.Q.obj Q)).commShiftIso n).hom.app
          (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₁Iso P Q A.mateTensor n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app
          (CochainComplex.mapBifunctor P Q A.mateTensor) ≫
        (shiftFunctor A.mateDerived n).map (a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩))) ∧
  (∀ (P Q : CochainComplex A.mateModules ℤ) (hP : A.mateFlat P) (hQ : A.mateFlat Q)
      (n : ℤ) (hQn : A.mateFlat (Q⟦n⟧)),
    a.representative.hom.app (⟨P, hP⟩, ⟨Q⟦n⟧, hQn⟩) ≫
        A.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
          ((DerivedCategory.Q.commShiftIso n).hom.app Q)) ≫
        (((Functor.curryObj A.tensor).obj (DerivedCategory.Q.obj P)).commShiftIso n).hom.app
          (DerivedCategory.Q.obj Q) =
      DerivedCategory.Q.map (CochainComplex.mapBifunctorShift₂Iso P Q A.mateTensor n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app
          (CochainComplex.mapBifunctor P Q A.mateTensor) ≫
        (shiftFunctor A.mateDerived n).map (a.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)))

def RingedTensorModel.MateCanonicalUnit {A : RingedTensorCorner.{u, w}}
    (a : RingedTensorModel A) (r : ∀ U : A.mateDerived, A.tensor.obj (U, A.mateUnit) ≅ U) :
    Prop :=
  ∃ hunit : A.mateFlat A.mateUnitComplex,
    ∀ (P : CochainComplex A.mateModules ℤ) (hP : A.mateFlat P),
      ∃ j : CochainComplex.mapBifunctor P A.mateUnitComplex A.mateTensor ≅ P,
        (∀ n : ℤ,
          CochainComplex.ιMapBifunctor P A.mateUnitComplex A.mateTensor n 0 n (add_zero n) ≫
              j.hom.f n =
            (A.mateTensor.obj (P.X n)).map
                (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                  (SheafOfModules.unit ((sheafCompose A.topology
                    (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring))).hom ≫
              ((monoidalCategory A.ring).rightUnitor (P.X n)).hom) ∧
        a.representative.hom.app (⟨P, hP⟩, ⟨A.mateUnitComplex, hunit⟩) ≫
          (r (DerivedCategory.Q.obj P)).hom = DerivedCategory.Q.map j.hom

def derivedTensor : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules R) ⥤
    DerivedCategory (Modules R) := Functor.curry.obj (selectedTensorPresentation R).derivedTensor

attribute [local irreducible] derivedTensor
```

## New

```lean
noncomputable abbrev RingedTensorCorner.mateUnitComplex (A : RingedTensorCorner.{u, w}) :=
  letI := monoidalCategory A.ring
  HomologicalComplex.tensorUnit A.mateModules (.up ℤ)

noncomputable abbrev RingedTensorCorner.mateTensor (A : RingedTensorCorner.{u, w}) :=
  KFlatFixedTensor.ordinaryTensor A.ring

def RingedTensorModel.MateCanonicalShifts {A : RingedTensorCorner.{u, w}}
    (a : RingedTensorModel A) [(Functor.curryObj A.tensor).CommShift₂Int] : Prop :=
  letI := monoidalCategory A.ring
  letI := ringedTensorPreadditive A.ring
  MateCanonicalShiftData A.mateTensor DerivedCategory.Q A.tensor A.mateFlat
    (fun P Q hp hq ↦ a.mateRepresentative.app (⟨P, hp⟩, ⟨Q, hq⟩))

def RingedTensorModel.MateCanonicalUnit {A : RingedTensorCorner.{u, w}}
    (a : RingedTensorModel A) (r : ∀ U : A.mateDerived, A.tensor.obj (U, A.mateUnit) ≅ U) :
    Prop :=
  letI := monoidalCategory A.ring
  letI := ringedTensorPreadditive A.ring
  MateCanonicalUnitData A.mateTensor DerivedCategory.Q A.tensor A.mateFlat A.mateUnitComplex
    (fun P n ↦ (A.mateTensor.obj (P.X n)).map
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (SheafOfModules.unit ((sheafCompose A.topology
          (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring))).hom ≫
      ((monoidalCategory A.ring).rightUnitor (P.X n)).hom)
    (fun P Q hp hq ↦ a.mateRepresentative.app (⟨P, hp⟩, ⟨Q, hq⟩)) r

def derivedTensor : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules R) ⥤
    DerivedCategory (Modules R) := Functor.curry.obj
      (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R)
```

The six additional public interface declarations in the item are
RingedTensorCorner.mateRepresentativeSource, RingedTensorCorner.mateRepresentativeTarget,
RingedTensorModel.mateRepresentative, RingedTensorModel.mateRepresentative_eq,
MateCanonicalShiftData and MateCanonicalUnitData. The first three are explicit constructions;
the equality theorem is rfl. The last two are the unchanged normalization formulas with
category, tensor, localization and representative comparison supplied as parameters.

## Users

The following is the union of the textual users reported by tools/downstream.py --uses for
mateUnitComplex, mateUnit, mateTensor, MateCanonicalShifts, MateCanonicalUnit and derivedTensor,
scanning downstream of all three changed modules together. This includes the users added
to the fixed-tensor module's downstream closure by the item's new public import. Its derivedTensor search conservatively includes other
namespaces with that last component. No downstream statement or proof requires adaptation:
the changed definitions are definitionally equal to their former bodies. Unchanged copies in
the sandbox are verification inputs and are not changes to another holder's work.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Algebra.Homology.ExactPullbackSignedComparison | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Algebra.Homology.FiniteFreeResolutionTensor | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated | unclaimed | Direct published tensor definition; existing proof adjustment. |
| Sheaf.Algebra.Homology.LineUnboundedDerivedTensor | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Algebra.Homology.SignedLineDerivedBaseChange | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGenericEvaluationCoherence | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleTorIntervalTriangle | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleProEtale | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.CategoryTheory.KoszulFibreLinearDescent | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.CategoryTheory.KoszulTensorDerivedTower | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.AffineLinePuritySource | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.BoundaryBoundedTensorComparison | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.CoefficientProjectionSquare | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.CoefficientPushFilteredLegs | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.DerivedCompletedTensorBilinearity | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.DerivedNakayamaResolution | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.DualizingUnitComposite | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.EtaleProperCoefficientTensorUnit | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.ExceptionalCoefficientComparison | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.ExternalComparisonTriangles | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDirectImage | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.FiniteOpenProductSwap | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | N1 | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.HomUniversalCoefficients | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.IntegralOpenExtensionReduction | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.InternalAdjunctionPairingChange | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.InternalHomDualTorAmplitude | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.NearbyGeometricSlice | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.OrientationEtaleCoefficientTwists | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.OrientationEtaleFamily | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.OrientedNearbyCycles | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.OrientedNearbyStrictLocalDescription | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.PeriodicTensorNormalForm | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.ProEtaleProjectiveCoefficient | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.ProjectionMateExact | C6 | Assigned proof and definitionally equal normalization interfaces. |
| Sheaf.Paper.ProperEtaleOriginScalarData | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.PullbackTensorCanonicalShiftUnit | unclaimed | Add a proved joint representative naturality API. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.RingedProjectionCoherenceData | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.RingedProjectionFirstShift | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.RingedSitePerfectProjectionFormula | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.RingedStrictTowerProjectionMorphism | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.ScalarModelFiniteFlatResolution | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.SectionDerivedRealization | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.SectionDerivedTensorNormalization | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.StrictAugmentedCoefficientPresentation | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.StrictPerfectTowerProjection | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.StrictProjectionCoaugmentation | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.StrictQuotientExchangeUnitEquation | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Paper.VectorTensorSiteEquations | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SixFunctors.ClosedImmersionTensorProjection | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SixFunctors.EtaleOpenScalarCoherence | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SixFunctors.EtaleOpenTensor | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SixFunctors.EtaleOpenTensorDefs | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SixFunctors.IntTensorProjection | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SixFunctors.OpenImmersionTensorProjection | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | Definitionally unchanged interface or a distinct namespace; no adaptation. |

## Status

landed 20261022T040151-L-2818727 2026-10-22 (merge of deliver/C6/Sheaf.Paper.ProjectionMateExact)
