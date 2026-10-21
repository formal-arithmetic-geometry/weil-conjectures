# integralScalarReductionConcrete, integralScalarReductionConcrete_additive, integralScalarReduction, integralScalarReduction_eqConcrete, integralScalarReductionIso, integralScalarReduction_additive, integralScalarTensorSection, integralScalarOrdinaryLevel, integralScalarOrdinaryLevel_additive, integralScalarLevel, integralScalarTowerFunctor, integralScalarComplexFunctor, integralScalarDerivedAction

## Reason

Construct ordinary coefficient change by sectionwise extension followed by sheafification.
The old derived-change-of-rings witness fixes exactly these objects and maps, so this
construction represents the same functor. The existing witness declaration is retained.
The ordinary functor is selected from the singleton consisting of this explicitly
constructed functor. The proved equality `integralScalarReduction_eqConcrete` and its
comparison isomorphism expose that construction where needed. This maintains a small
abstract interface for consumers and prevents repeated normalization of coefficient limits.
There is no arbitrary existence choice: equality to one constructed functor uniquely fixes
all the chosen data, using the proved `existsUnique_eq` theorem.

Tensor sections are the literal sheafified pure tensors transported through that canonical
comparison isomorphism. This is the same generator as in the old witness-based formula.
The additive instance transports the proved additivity of the concrete functor. Private
naturality, extensionality and balancing proofs use the comparison and its inverse laws.

The new ordinary-level functor names extension followed by restriction. Prolonging this
composite to complexes is definitionally the composite of the two prolongations. The level
functor uses this presentation to keep termwise-transition comparisons small. Explicit
annotations on the tower and Roos functors preserve their previously inferred types
while avoiding repeated expansion of the completed module categories. The ordinary
construction retains the original commutative coefficient presentation in its source
category and preadditive instances.

The derived scalar action selects the unique transformation equal to the canonical fully
faithful preimage. Its proved equality and component formula expose the original action.
This is another singleton choice with a completely proved defining equality. Parametric
localization lemmas check the scalar compatibility before substituting the concrete lift.
Functor-level equalities identify the selected localization compositions and avoid repeating
that comparison at concrete cone objects.

The definitions used by the targets require the normal independent statement review.
The ordinary tensor functor, its tensor generators and scalar action have the same
mathematical meanings; no target signature changes.

## Old

```lean
noncomputable def integralScalarReduction (n : ℕ) :
    integralTowerModules l E Y ⥤ integralOperationsFiniteModules l L Y n :=
  (integralScalarReductionWitness l E L ι Y n).choose
```

```lean
noncomputable instance integralScalarReduction_additive (n : ℕ) :
    (integralScalarReduction l E L ι Y n).Additive :=
  (integralScalarReductionWitness l E L ι Y n).choose_spec.choose_spec.choose_spec.choose
```

```lean
noncomputable def integralScalarTensorSection (n : ℕ)
    (M : integralTowerModules l E Y) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L Y n).obj.obj U) (x : M.val.obj U) :
    ((integralScalarReduction l E L ι Y n).obj M).val.obj U :=
  (eqToHom ((integralScalarReductionWitness l E L ι Y n).choose_spec.choose M).symm).val.app U
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (SheafOfModules.changeOfRingsPresheaf
        (integralScalarRho l E L ι Y n) M).presheaf).app U
          (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
            ((integralScalarRho l E L ι Y n).hom.app U).hom] x))
```

```lean
noncomputable def integralScalarLevel (n : ℕ) :=
  integralScalarFiniteComplex l E L ι Y n ⋙ integralOperationsRestrict l L Y n
```

```lean
noncomputable def integralScalarTowerFunctor :=
  (Functor.ofOpSequence (X := fun n ↦ integralScalarLevel l E L ι Y n)
    (integralScalarTransition l E L ι Y)).flip
```

```lean
noncomputable def integralScalarComplexFunctor :=
  integralScalarTowerFunctor l E L ι Y ⋙ integralOperationsRoosFunctor
```

```lean
noncomputable def integralScalarDerivedAction (a : Padic.coefficientExtensionIntegers l E) :
    𝟭 (DerivedCategory (integralTowerModules l E Y)) ⟶
      𝟭 (DerivedCategory (integralTowerModules l E Y)) :=
  (Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (integralTowerModules l E Y) (ComplexShape.up ℤ))
    (DerivedCategory (integralTowerModules l E Y))).preimage
      (whiskerRight (integralScalarChainAction l E Y a) DerivedCategory.Q)
```

## New

```lean
noncomputable def integralScalarReductionConcrete (n : ℕ) :
    integralTowerModules l E Y ⥤ integralOperationsFiniteModules l L Y n :=
  let φ := integralScalarRho l E L ι Y n
  let E₀ : SheafOfModules.{max u (t + 1)}
      (SheafOfModules.derivedChangeRingIndependentCoefficients
        (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (completedIntegralCommRingSheafUnrestricted l E Y)) ⥤
      PresheafOfModules.{max u (t + 1)}
      (SheafOfModules.derivedChangeRingIndependentCoefficients
        (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (integralCoefficientCommRingSheaf l L Y n)).obj :=
    { obj := SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)} φ
      map := fun a ↦
        { app := fun U ↦ (ModuleCat.extendScalars (φ.hom.app U).hom).map (a.val.app U)
          naturality := SheafOfModules.changeOfRingsHom_naturality.{t, t + 1, max u (t + 1)} φ _ a }
      map_id := by
        intro M
        apply PresheafOfModules.hom_ext
        intro U
        simp
        rfl
      map_comp := by
        intro M N P a b
        apply PresheafOfModules.hom_ext
        intro U
        simp }
  E₀ ⋙ PresheafOfModules.sheafification.{max u (t + 1)}
    (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l L Y n)).obj)
```

```lean
noncomputable instance integralScalarReductionConcrete_additive (n : ℕ) :
    (integralScalarReductionConcrete l E L ι Y n).Additive := by
  let φ := integralScalarRho l E L ι Y n
  have hscalar (U : Y.ProEtᵒᵖ) :
      (ModuleCat.extendScalars (φ.hom.app U).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (φ.hom.app U).hom).left_adjoint_additive
  let S := PresheafOfModules.sheafification.{max u (t + 1)}
    (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l L Y n)).obj)
  have : S.Additive :=
    (PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
      (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients
        (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (integralCoefficientCommRingSheaf l L Y n)).obj)).left_adjoint_additive
  constructor
  intro M N a b
  change S.map _ = S.map _ + S.map _
  rw [← S.map_add]
  congr 1
  apply PresheafOfModules.hom_ext
  intro U
  simpa only [SheafOfModules.add_val, PresheafOfModules.add_app] using
    (ModuleCat.extendScalars (φ.hom.app U).hom).map_add
      (f := a.val.app U) (g := b.val.app U)
```

```lean
noncomputable def integralScalarReduction (n : ℕ) :
    integralTowerModules l E Y ⥤ integralOperationsFiniteModules l L Y n :=
  (existsUnique_eq (a' := integralScalarReductionConcrete l E L ι Y n)).exists.choose
```

```lean
theorem integralScalarReduction_eqConcrete (n : ℕ) :
    integralScalarReduction l E L ι Y n = integralScalarReductionConcrete l E L ι Y n :=
  (existsUnique_eq (a' := integralScalarReductionConcrete l E L ι Y n)).exists.choose_spec
```

```lean
noncomputable def integralScalarReductionIso (n : ℕ) :
    integralScalarReduction l E L ι Y n ≅ integralScalarReductionConcrete l E L ι Y n :=
  eqToIso (integralScalarReduction_eqConcrete l E L ι Y n)
```

```lean
noncomputable instance integralScalarReduction_additive (n : ℕ) :
    (integralScalarReduction l E L ι Y n).Additive := by
  rw [integralScalarReduction_eqConcrete]
  infer_instance
```

```lean
noncomputable def integralScalarTensorSection (n : ℕ)
    (M : integralTowerModules l E Y) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L Y n).obj.obj U) (x : M.val.obj U) :
    ((integralScalarReduction l E L ι Y n).obj M).val.obj U :=
  ((integralScalarReductionIso l E L ι Y n).inv.app M).val.app U
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (SheafOfModules.changeOfRingsPresheaf
        (integralScalarRho l E L ι Y n) M).presheaf).app U
          (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
            ((integralScalarRho l E L ι Y n).hom.app U).hom] x))
```

```lean
noncomputable def integralScalarOrdinaryLevel (n : ℕ) :
    integralTowerModules l E Y ⥤ integralTowerModules l L Y :=
  (integralScalarReduction l E L ι Y n ⋙
    SheafOfModules.restrictScalars.{max u (t + 1)}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l L Y n)))
```

```lean
instance integralScalarOrdinaryLevel_additive (n : ℕ) :
    (integralScalarOrdinaryLevel l E L ι Y n).Additive :=
  inferInstanceAs ((integralScalarReduction l E L ι Y n ⋙
    SheafOfModules.restrictScalars.{max u (t + 1)}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
          (completedIntegralCommRingProjectionUnrestricted l L Y n))).Additive)
```

```lean
noncomputable def integralScalarLevel (n : ℕ) :=
  (integralScalarOrdinaryLevel l E L ι Y n).mapHomologicalComplex (ComplexShape.up ℤ)
```

```lean
noncomputable def integralScalarTowerFunctor :
    CochainComplex (integralTowerModules l E Y) ℤ ⥤
      (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l L Y) ℤ) :=
  (Functor.ofOpSequence (X := fun n ↦ integralScalarLevel l E L ι Y n)
    (integralScalarTransition l E L ι Y)).flip
```

```lean
noncomputable def integralScalarComplexFunctor :
    CochainComplex (integralTowerModules l E Y) ℤ ⥤
      CochainComplex (integralTowerModules l L Y) ℤ :=
  integralScalarTowerFunctor l E L ι Y ⋙ integralOperationsRoosFunctor
```

```lean
noncomputable def integralScalarDerivedAction (a : Padic.coefficientExtensionIntegers l E) :
    𝟭 (DerivedCategory (integralTowerModules l E Y)) ⟶
      𝟭 (DerivedCategory (integralTowerModules l E Y)) :=
  (existsUnique_eq (a' :=
    (Localization.fullyFaithfulWhiskeringLeft
      (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
      (HomologicalComplex.quasiIso (integralTowerModules l E Y) (ComplexShape.up ℤ))
      (DerivedCategory (integralTowerModules l E Y))).preimage (X := 𝟭 _) (Y := 𝟭 _)
        (whiskerRight (integralScalarChainAction l E Y a) DerivedCategory.Q)
  )).exists.choose
```

## Users

Return C-adc97682f named five additional consumers absent from the previous table.
All five are now listed below after inspection of their current declarations.
The changes preserve the specified tensor generators, quotient-tower maps,
Roos complexes and canonical derived action used by those consumers.
No consumer source adaptation is delivered.

The table retains the 232 transitive importers checked for the previous delivery, plus
all current textual users of the changed declarations and the repaired module.
The 2026-10-21 refresh of `tools/downstream.py --uses` adds the six users named in
return C-05da8 and `Sheaf.Paper.SfIntegralConstructibleLinear`. Their current
claim holders are recorded in the table below. The tensor generators, strict quotient
towers, Roos complex and canonical derived scalar action keep the same meaning
in the normalization predicates and constructions of these users.

The previous delivery checked twelve consumer modules, including its direct
importers, both shift modules and scalar-action users, unchanged against the
repaired artifact. The return repair additionally checks the seven users added
below; the report records their current compiler results and baseline limitations.
The action is proved
equal to the original canonical lift, so its mathematical meaning is preserved in all users.
Claim holders are recorded from the current `coord/claims` entries.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedSiteTorFlatModel | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Algebra.Homology.SitePerfectLowerModel | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Algebra.Homology.SitePerfectOpcyclesRetract | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Algebra.Homology.SitePerfectTorWindow | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Algebra.Homology.SitePerfectUpperModel | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.ExcellentBaseGenericCurvePreparation | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.ExceptionalContractionDiamond | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.FiniteBirationalNodalConnectedIso | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.FiniteConstantLocalModel | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.GeometricSpecializationCategory | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.GeometricallyReducedEtaNormal | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.MultipointedCurveModification | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.OrdinaryMultiplePoint | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.OrdinaryPointDeltaBranches | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.SemistableMultipointedPair | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.StableModificationStabilityLocus | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.StrictlySemistableCurve | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.StrictlySemistableModelNormal | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.ValuationStableBlowdownUniqueness | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.CategoryTheory.SiteTorIntervalRestriction | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.CategoryTheory.Sites.CoherentConservativeReflection | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.CategoryTheory.Sites.CoherentEpimorphicQuotient | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.CategoryTheory.Sites.CoherentObjectApproximation | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.CategoryTheory.Sites.CoherentToposRepair | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.CategoryTheory.Sites.FiniteCoproductToposCoherent | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.CategoryTheory.Sites.FiniteLocallyConstantCoherent | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.CategoryTheory.Sites.OrientedAffineSliceSite | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.AlgebraicallyClosedCoefficients | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.AlterationBlowupFinite | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.AlterationFiniteRefinement | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.BoundedConstructibleBaseChange | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.BoundedConstructiblePushforwardRestriction | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.ClopenRoosIntegralDescent | unclaimed | The clopen restriction comparison still uses the same quotient tower and sheafified pure tensors in its section formula; its mathematical statement is unchanged. Compiled unchanged against the freshly rebuilt artifact (24.3 s); no adaptation needed. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.CoefficientExtensionReductionModel | E6 | Compiled unchanged against the repaired module artifact; signatures preserved. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.CoefficientTwistsDetailed | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.CoherentSetCriterion | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.CompleteResidueCohomologyBounds | X3 | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.CompletedLineComplete | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.CompletedLineDerived | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.CompletedScalarChainShift | unclaimed | Compiled unchanged against the repaired module artifact; signatures preserved. |
| Sheaf.Paper.CompletedScalarShift | unclaimed | Compiled unchanged against the repaired module artifact; signatures preserved. |
| Sheaf.Paper.CompletedScalarShiftDescent | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.CondensedPointCoefficients | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.CondensedPointDiscreteConstantComparison | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.ConstantCoefficientObjectsConstructible | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | unclaimed | Tensor generators and the strict tower/Roos normalization retain the same meaning. Compiled unchanged against the clean repaired artifact; no source adaptation needed. |
| Sheaf.Paper.ConstantScalarStrictUnit | X2 | The strict unit still has the specified Roos target, one-minus-shift boundary and pure-tensor quotient coordinates; the normalization predicates keep their meaning. Compiled unchanged against the freshly rebuilt artifact (9.6 s); no adaptation needed. |
| Sheaf.Paper.ConstantScalarUnitQuasiIsomorphism | X3 | The regular-complex quotient tower, its Roos complex and normalized unit legs keep the same objects and maps; limit and quasi-isomorphism assertions are unchanged. Compiled unchanged against the freshly rebuilt artifact (8.9 s); no adaptation needed. |
| Sheaf.Paper.ConstantToContinuousScalarFlat | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.ConstructibleFlatCohomologyTorBound | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.ConstructibleHeart | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.ConstructibleStandardTStructure | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.DerivedCompleteOnSlices | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.DerivedCompleteUnrestricted | unclaimed | Compiled unchanged against the repaired module artifact; signatures preserved. |
| Sheaf.Paper.EtaleIntegralLineDerivedComplete | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.ExceptionalAdjointAdmissibility | unclaimed | Compiled unchanged against the repaired module artifact; signatures preserved. |
| Sheaf.Paper.FdCoefficientComparison | A2 | The coefficient-comparison normalization uses the same completed scalar complex. Current source has identical instance-synthesis and follow-on errors against baseline and clean repaired artifact; see report. No source adaptation delivered. |
| Sheaf.Paper.FiniteConstantModelResolution | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.FiniteFreeCompletedScalarComparison | H7 | Compiled unchanged against the repaired module artifact; signatures preserved. |
| Sheaf.Paper.FiniteStagePairCategory | H8 | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.FormalClosedSupportDerived | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.FormalClosedSupportSheaves | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.GeneralNearbySliceTest | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.HomUniversalCoefficients | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.IntegralCanonicalTruncations | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | The identity reduction tower and its morphism remain the same strict quotient tower. Compiled unchanged against the clean repaired artifact; no source adaptation needed. |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed | The scalar realization normalization still tests the same sheafified tensor generators. Compiled unchanged against the clean repaired artifact; no source adaptation needed. |
| Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.IntegralConstructibleLinear | unclaimed | Compiled unchanged against the repaired module artifact; signatures preserved. |
| Sheaf.Paper.IntegralLineTensorComparison | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.IntegralLineTensorComparisonDefinitions | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.IntegralLineTensorComparisonIso | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.IntegralLineTensorComparisonRepresentative | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.IntegralLineTensorCompleteness | S5 | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.IntegralModelSurjectiveClosedReflection | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.IntegralOperationsScalarComparisons | U1 | Compiled unchanged against the repaired module artifact; signatures preserved. |
| Sheaf.Paper.IntegralOperationsScalarExtension | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.IntegralScalarExtension | unclaimed | Compiled unchanged against the repaired module artifact; signatures preserved. |
| Sheaf.Paper.IntegralScalarExtensionConstructible | unclaimed | Compiled unchanged against the repaired module artifact; signatures preserved. |
| Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic | unclaimed | Compiled unchanged against the repaired module artifact; signatures preserved. |
| Sheaf.Paper.IntegralScalarExtensionUniverses | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.IntegralScalarExtensionWellDefined | U2 | Construction and proof repaired; existing theorem statements preserved. |
| Sheaf.Paper.IntegralStratifiedPerfectCharacterization | H9 | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.IntegralStratifiedPerfectClosureHomology | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.IntegralTStructure | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.IsomorphismScalarTensorKFlatModel | S6 | Ordinary scalar reduction and its tensor generators still define the same finite, quotient and transition formulas; local irreducibility attributes remain valid. Compiled unchanged against the freshly rebuilt artifact (9.5 s); no adaptation needed. |
| Sheaf.Paper.LocalizedTStructure | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.ModificationClosedImageLifting | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.ModificationsZariskiRefinement | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.NearbyClosedImage | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.NearbyGeometricSlice | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.NearbyProperHyperdescent | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.NearbySpreadOut | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.OrgogozoInductionData | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.OrientedClosedBaseRestriction | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.OrientedConstructibleCoherent | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.OrientedConstructibleSetSheaf | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.OrientedConstructibleSheaf | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.OrientedConstructibleSheafVanishing | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.OrientedConstructibleSubquotients | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.OrientedHypercoverDescentDatum | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.OrientedMaximalPointFiniteness | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.OrientedNearbyCycles | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.OrientedProductPointsConservative | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.OrientedProperFibreExchange | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.OrientedSourceLocalization | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.PbcAutomorphismTransport | F3 | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.PbcFilteredRetractDescent | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.PbcFiniteCompletedCoefficientMap | unclaimed | Compiled unchanged against the repaired module artifact; signatures preserved. |
| Sheaf.Paper.PbcWeilCategory | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Tower balancing and completed evaluation still use the specified pure tensors and Roos maps. Compiled unchanged against the clean repaired artifact; no source adaptation needed. |
| Sheaf.Paper.PointSectionsScalarExtension | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.PointSectionsTensorShift | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.ProperUnboundedWindowBounded | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.PsiConstructibilityDescent | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.PurTwistSheafLocallyFree | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.RationalSliceCompletedEvaluation | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.RationalThickEvaluation | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.RationalizationIdempotentComplete | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.RationalizationKaroubi | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.ScalarExtensionComposition | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.ScalarExtensionExact | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | unclaimed | The quotient-model section still transports the same pure tensor through its evaluation iso. Compiled unchanged against the clean repaired artifact (47.6 s); no source adaptation needed. |
| Sheaf.Paper.SfIntegralConstructibleLinear | unclaimed | The scalar-action normalization still uses the same canonical derived scalar action. Compiled unchanged against the clean repaired artifact; no source adaptation needed. |
| Sheaf.Paper.SfIntegralDirectImageConstructible | E9 | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.SfIntegralStandardTruncations | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.SfRationalLocalGlobalPowerTorsion | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.SignedLineTensorEquivalence | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.StratifiedOrientedCover | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.StratifiedPerfectInternalHomCoproducts | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.TAdmissibleCoefficientModels | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Paper.WeilTensorProduct | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.SixFunctors.BrownHypothesesAmbient | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.SixFunctors.CompletedCoefficientFreeResolution | M6 | The uniformizer acts through the same canonical derived scalar action; the reduction triangle and its actual reductionMap retain their meaning. Compiled unchanged against the freshly rebuilt artifact (6.2 s); no adaptation needed. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.SixFunctors.TraceFormula.NodalEtaleChart | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.SixFunctors.TraceFormula.NodalLogRegularity | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.Topology.ProfiniteCondensedRing | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ClosedImageGenericAlteration | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ContractedComponentGenericData | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ContractedComponentNoExtraGeneric | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.CurveP1TreeLocalCriterion | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.FinitarySiteCoherentGenerators | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.FiniteEtaModificationGluing | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.LocalMarkingLength | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.MarkedCurveFiniteTypeModel | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.NodalContractionNormalizationBranches | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.OrientedPointCohomology | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.OrientedPointNormalizedStratum | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ProjectiveLineTree | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ProperBaseChangeCoherentConservative | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ReducedFibreModification | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.SemistableMarkedPoint | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.StableCurveDiagramNoetherianModel | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.StableModificationConstructibility | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.StableModificationSpreading | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.StableModificationStabilityFieldDescent | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ValuationHorizontalCurveModels | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ValuationReducedFibreNormalization | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| Sheaf.TraceFormula.ValuationSymmetricNodalBlowup | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Transitive importer; signatures and mathematical construction unchanged; no edit needed. |

## Status

landed 20261021T140929-L-2776424 2026-10-21 (merge of deliver/U2/Sheaf.Paper.IntegralScalarExtensionWellDefined)
