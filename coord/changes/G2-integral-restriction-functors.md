# IntegralRestriction.tateLine, pullTwistShift, restrictedPull, restrictedPush, brownComparison

## Reason

The three independent geometric arguments need the canonical functors without importing their own assembled theorem. Move all five definitions verbatim into IntegralRestrictionFunctors and publicly re-export them from IntegralRestrictionLine. No mathematical definition, signature, visibility, universe, scalar action, or target changes. No arbitrary object is chosen. Existing source-library files are untouched.

## Old

In lean/Sheaf/SixFunctors/IntegralRestrictionLine.lean:

```lean
/-- The published signed Tate line, transported back to internal modules by the existing
sectionwise module equivalence. No new coefficient line or scalar action is chosen.
Source: blueprint sk-thm-int-restriction-line, Tate twist convention
(blueprint: det-thm-int-restriction-line). -/
def tateLine (X : Scheme.{u}) (d : ℤ) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X)
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)).inverse.obj
      (spSignedTwist X _ (spIntegralTwist X ℓ E) d)

/-- The actual functor f^*(-)(d)[2d]: derived pullback, right tensor with the published
Tate line in degree zero, and shift by 2d.
Source: blueprint sk-thm-int-restriction-line, displayed right adjoints
(blueprint: det-thm-int-restriction-line). -/
def pullTwistShift {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    IntegralCompactSupport.Ambient (Profinite.padicIntegersRingObj ℓ E.val) Y ⥤
      IntegralCompactSupport.Ambient (Profinite.padicIntegersRingObj ℓ E.val) X :=
  IntegralCompactSupport.pull (Profinite.padicIntegersRingObj ℓ E.val) f ⋙
    (derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) X).flip.obj
      ((DerivedCategory.singleFunctor _ 0).obj (tateLine ℓ E X (d : ℤ))) ⋙
    shiftFunctor _ (2 * (d : ℤ))

/-- Restriction of f^*(-)(d)[2d] to the recorded Loc(Dbc) categories. The membership
witness only restricts its codomain and does not replace any functor or morphism.
Source: blueprint sk-thm-int-restriction-line, localizing-category convention
(blueprint: det-thm-int-restriction-line). -/
def restrictedPull {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (h : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X
        ((pullTwistShift ℓ E f d).obj K)) :
    (IntegralCompactSupport.localizing
      (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
    (IntegralCompactSupport.localizing
      (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory :=
  (IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X).lift
    ((IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).ι ⋙
      pullTwistShift ℓ E f d) (fun K ↦ h K.obj K.property)

/-- Restriction of the actual Rf_* to Loc(Dbc), once its preservation is supplied.
Source: blueprint sk-thm-int-restriction-line, projective-line left adjoint
(blueprint: det-thm-int-restriction-line). -/
def restrictedPush {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) X K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val) f).obj K)) :
    (IntegralCompactSupport.localizing
      (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory ⥤
    (IntegralCompactSupport.localizing
      (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory :=
  (IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).lift
    ((IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X).ι ⋙
      IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val) f)
    (fun K ↦ h K.obj K.property)

/-- Comparison with any Brown right adjoint for the chosen boundary compactification.
Brown's theorem does not choose an adjoint, so its isomorphism class is stated using
its defining adjunction. Quantification over compactifications includes the fixed one.
Source: blueprint sk-thm-int-restriction-line, the two f^! comparisons
(blueprint: det-thm-int-restriction-line). -/
def brownComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
      (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory) : Prop :=
  ∀ (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) X K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.image (Profinite.padicIntegersRingObj ℓ E.val)
          c.obj.obj).obj K))
    (J : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
      (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory),
    Nonempty (IntegralCompactSupport.lowerShriek
      (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣ J) → Nonempty (J ≅ G)
```

## New

In lean/Sheaf/SixFunctors/IntegralRestrictionFunctors.lean, publicly imported by the original module:

```lean
/-- The published signed Tate line, transported back to internal modules by the existing
sectionwise module equivalence. No new coefficient line or scalar action is chosen.
Source: blueprint sk-thm-int-restriction-line, Tate twist convention
(blueprint: def-sfb-integral-restriction-functors). -/
def tateLine (X : Scheme.{u}) (d : ℤ) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X)
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)).inverse.obj
      (spSignedTwist X _ (spIntegralTwist X ℓ E) d)

/-- The actual functor f^*(-)(d)[2d]: derived pullback, right tensor with the published
Tate line in degree zero, and shift by 2d.
Source: blueprint sk-thm-int-restriction-line, displayed right adjoints
(blueprint: def-sfb-integral-restriction-functors). -/
def pullTwistShift {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    IntegralCompactSupport.Ambient (Profinite.padicIntegersRingObj ℓ E.val) Y ⥤
      IntegralCompactSupport.Ambient (Profinite.padicIntegersRingObj ℓ E.val) X :=
  IntegralCompactSupport.pull (Profinite.padicIntegersRingObj ℓ E.val) f ⋙
    (derivedTensor (Profinite.padicIntegersRingObj ℓ E.val) X).flip.obj
      ((DerivedCategory.singleFunctor _ 0).obj (tateLine ℓ E X (d : ℤ))) ⋙
    shiftFunctor _ (2 * (d : ℤ))

/-- Restriction of f^*(-)(d)[2d] to the recorded Loc(Dbc) categories. The membership
witness only restricts its codomain and does not replace any functor or morphism.
Source: blueprint sk-thm-int-restriction-line, localizing-category convention
(blueprint: def-sfb-integral-restriction-functors). -/
def restrictedPull {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (h : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X
        ((pullTwistShift ℓ E f d).obj K)) :
    (IntegralCompactSupport.localizing
      (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
    (IntegralCompactSupport.localizing
      (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory :=
  (IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X).lift
    ((IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).ι ⋙
      pullTwistShift ℓ E f d) (fun K ↦ h K.obj K.property)

/-- Restriction of the actual Rf_* to Loc(Dbc), once its preservation is supplied.
Source: blueprint sk-thm-int-restriction-line, projective-line left adjoint
(blueprint: def-sfb-integral-restriction-functors). -/
def restrictedPush {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) X K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val) f).obj K)) :
    (IntegralCompactSupport.localizing
      (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory ⥤
    (IntegralCompactSupport.localizing
      (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory :=
  (IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y).lift
    ((IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) X).ι ⋙
      IntegralCompactSupport.push (Profinite.padicIntegersRingObj ℓ E.val) f)
    (fun K ↦ h K.obj K.property)

/-- Comparison with any Brown right adjoint for the chosen boundary compactification.
Brown's theorem does not choose an adjoint, so its isomorphism class is stated using
its defining adjunction. Quantification over compactifications includes the fixed one.
Source: blueprint sk-thm-int-restriction-line, the two f^! comparisons
(blueprint: def-sfb-integral-restriction-functors). -/
def brownComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
      (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory) : Prop :=
  ∀ (c : Compactification.BoundaryCompactification f)
    (h : ∀ K, IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) X K →
      IntegralCompactSupport.localizing (Profinite.padicIntegersRingObj ℓ E.val) Y
        ((IntegralCompactSupport.image (Profinite.padicIntegersRingObj ℓ E.val)
          c.obj.obj).obj K))
    (J : (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) Y).FullSubcategory ⥤
      (IntegralCompactSupport.localizing
        (Profinite.padicIntegersRingObj ℓ E.val) X).FullSubcategory),
    Nonempty (IntegralCompactSupport.lowerShriek
      (Profinite.padicIntegersRingObj ℓ E.val) c.obj.obj h ⊣ J) → Nonempty (J ≅ G)
```

Only the module location and blueprint attachment change. Each old name is the same public declaration with the same body and statement. Byte-for-byte comparison of the assembled theorem signature passed. The old public imports remain public in the original module and the new interface. No target definition changes meaning, so the target statement review is preserved.

## Users

`tools/downstream.py Sheaf.SixFunctors.IntegralRestrictionLine --uses tateLine pullTwistShift restrictedPull restrictedPush brownComparison` was checked. The only external short-name hit is an unrelated tateLine in WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin. All transitive consumers retain the same public declarations and imports. No consumer needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.DeligneLaumon.QbarCurveDuality | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.ArithmeticRoots | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.CommonStageFourierWeightUpper | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.CurveIntermediateExtension | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.ExceptionalInverseImageExistence | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.FiniteDncNormalizationReduction | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.FiniteTorStability | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.FixedStalkIdentificationReduction | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.GlobalVerdierDuality | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.ProperExceptionalRestriction | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.ProperProductCounitTranspose | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.QbarPerverseSubcategories | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.QbarPerverseSupportCondition | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.RationalHomScalarTranspose | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.RationalTensorSymmetry | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.SfBidualityClass | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.SitePerfectRationalBidual | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.SmoothPullbackSupportDimension | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.TateTwistSupportCondition | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.VerdierCoefficientRealization | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SecSmoothPurity.MixedBaseChange | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.CoefQbarVerdier | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.FiniteExceptional | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.IntegralDualizing | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.IntegralVerdier | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.RationalOperations | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.RationalRetractEvaluation | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.RationalVerdier | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SmoothPurity.NormalizedWitness | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.Targets.SmoothPurityQbar | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.ZetaWeil.WeightPurityRoots | not queried; not adapted | Same public definitions and signatures; unchanged. |
| TargetsCheck | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.PoincareDuality.Verdier | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.SmoothPurity.Defs | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.Statement | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.Additivity | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.BaseChangeCoherence | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.Basic | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.BorelMoore | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.CoefficientMorphism | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.CompactCohomology | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.CompactPullback | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.Correspondence | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.CorrespondencePair | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.CurvePieces | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.Dualizing | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.FibreCoherence | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.FibreModel | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.FixedPoint | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.FixedPointScheme | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.Frobenius | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.GenericQuotient | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.HomologyUnit | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.KunnethVerdier | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.LefschetzVerdier | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.LocalTerm | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.LocalTermLocality | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.Main | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.ModelExtension | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.OpenPieceCoherence | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.OpenSquare | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.PointNormalization | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.Product | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.ProperCompatibility | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.ProperCurve | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.ProperPushforward | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.PullbackFamily | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.RelativeFrobenius | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunction | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.Stalk | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.Statement | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.SupportedPairing | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.TraceClass | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.TraceClassAdditivity | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.WeilBaseChange | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.TraceFormula.WeilTrace | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.WeilSheaf.Curve | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.WeilSheaf.EulerProduct | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.WeilSheaf.LFunction | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.ZetaFunction.Examples | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.ZetaFunction.LissePurity | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.ZetaFunction.Rationality | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.ZetaFunction.TraceFormula | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.ZetaFunction.Weights | not queried; not adapted | Same public definitions and signatures; unchanged. |
| WeilConjectures.ZetaFunction.WeilObjectComparison | not queried; not adapted | Same public definitions and signatures; unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionLine | G2 | Assemble the original theorem; publicly re-export the definitions. |
| Sheaf.SixFunctors.IntegralRestrictionFunctors | new, G2 | Own the five unchanged definitions. |
| Sheaf.SixFunctors.IntegralTateLineConstructible | new, G2 | State the degree-zero constructibility subargument. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | new, G2 | State only the projective-line adjunction. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | new, G2 | State only the affine compact-support adjunction. |

## Status

landed 20261024T204607-L-3799780 2026-10-24 (merge of deliver/G2/Sheaf.SixFunctors.IntegralRestrictionLine)
