# AlgebraicGeometry.SupportHomPair.Identification

## Reason

Use the existing `SupportedHomChi` and `SupportedHomChiNatural` type aliases for
these two fields of the normalized identification. Both aliases unfold to exactly
the former field types. The group is the same support-hypercohomology object, and
the naturality map is the same composition of derived sections and homology.

This shares the types with `SupportedHomCocycleNormalization` and the transport
interface, instead of repeating the large derived-category type expressions during
conversion. The cocycle normalization field, field order, universes and all mathematical
parameters and quantifiers stay the same. Every existing public declaration type remains definitionally equal
to its original type; no property or normalization is added or removed.

All proof steps stay in the assigned module. The aliases are already available
through its public normalization interface, so no import changes are needed. No
adopted source-library declaration is changed. Targets using this definition need
renewed statement review; unfolding the aliases preserves their meaning.

## Old

```lean
structure Identification where
  chi : ∀ (K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ),
    S.group K a ≃+
      ((DerivedCategory.singleFunctor (Sheaf S.topology (ModuleCat.{u + 1} A)) 0).obj
        S.supported ⟶ K.obj⟦a⟧)
  naturality : ∀ (K L : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A)))
      (b : K ⟶ L) (a : ℤ) (x : S.group K a),
    chi L a ((S.sections.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a).map b x) =
        chi K a x ≫ (DerivedCategory.Plus.ι.map b)⟦a⟧'
  normalization : ∀ (I : CochainComplex.Plus (Sheaf S.topology (ModuleCat.{u + 1} A)))
      [∀ n : ℤ, Injective (I.obj.X n)] (a : ℤ)
      (f : S.supported ⟶ I.obj.X a) (hf : f ≫ I.obj.d a (a + 1) = 0)
      (x : (S.complex I).cycles a),
    kernel.ι ((I.obj.X a).obj.map S.restriction.op) ((S.complex I).iCycles a x) =
      ((constantSheafAdj S.topology (ModuleCat.{u + 1} A) S.isTerminal).homEquiv _ _
        (S.constantRestriction ≫ f)) 1 →
      chi (DerivedCategory.Plus.Q.obj I) a (S.cycleClass I a x) =
        S.cocycleMorphism I a f hf
```

## New

```lean
structure Identification where
  chi : SupportedHomChi S.topology A S.restriction S.supported
  naturality : SupportedHomChiNatural S.topology A S.restriction S.supported chi
  normalization : ∀ (I : CochainComplex.Plus (Sheaf S.topology (ModuleCat.{u + 1} A)))
      [∀ n : ℤ, Injective (I.obj.X n)] (a : ℤ)
      (f : S.supported ⟶ I.obj.X a) (hf : f ≫ I.obj.d a (a + 1) = 0)
      (x : (S.complex I).cycles a),
    kernel.ι ((I.obj.X a).obj.map S.restriction.op) ((S.complex I).iCycles a x) =
      ((constantSheafAdj S.topology (ModuleCat.{u + 1} A) S.isTerminal).homEquiv _ _
        (S.constantRestriction ≫ f)) 1 →
      chi (DerivedCategory.Plus.Q.obj I) a (S.cycleClass I a x) =
        S.cocycleMorphism I a f hf
```

## Users

The listed downstream statements keep the same normalized identification data.
The field types unfold to exactly the original formulas; their applications and
record constructors are unchanged. Searches found no downstream named applications
of these field arguments; no downstream adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.SupportedHomPullback` | B8 | Uses the existing chi and naturality type aliases, with the same fields and normalization. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.CartierClassAgreement` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.ClosedSupportedCupVanishing` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.LineZeroClassEtaleRealization` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.LocalizedTopChern` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityAffineLineOrientation` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityAffineLineOrientationInjectivity` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityAffineLineSupportStalk` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PurityExteriorProductFrame` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.VectorBundleDiagonalOrientation` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.VectorBundleThom` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.VectorBundleThomMaps` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.VectorBundleThomProduct` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | No change of statement or proof: the new body is definitionally equal. |
| `Sheaf.Paper.AffineDiagonalTensorCoordinates` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.AffineSpaceZeroSectionPurity` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |
| `Sheaf.Paper.ProjectionPurityAgreement` | unclaimed | No adaptation: the changed types and constructions remain definitionally equal. |

## Status

landed 20261022T025316-L-1272250 2026-10-22 (merge of deliver/B8/Sheaf.Paper.SupportedHomPullback)
