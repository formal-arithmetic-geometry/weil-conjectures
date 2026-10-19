# AlgebraicGeometry.ProEtale.integralTensorShriek_generated

## Reason

The completed proofs use local irreducibility attributes to keep categorical typeclass
elaboration from expanding the derived and module monoidal-closed structures and the
inverse-image comparison definitions. The additional universe is used by the private
triangulated-category helper. The scope and namespace opens support the new proofs.
The static preflight scanner flags these commands conservatively and requires this record.

Every original public declaration signature is textually identical to the current shared
source. The body of `integralTensorShriek_pointComplex` is also textually identical.
All public imports are retained, in their original order. New imports are proof-only;
`import all` exposes proved private lemmas only within this file. The irreducibility
attributes are local to the namespace. The only added definition, `stratumPresentation`,
is private and constructs an actual three-stratum stratification. No exported instance,
notation, definition, coefficient object, or target statement changes its meaning.

## Old

The changed existing commands were:

```lean
universe u
open scoped CategoryTheory.Obj
```

There were no local irreducibility attributes, no additional namespace opens below the
preservation theorem, and no `stratumPresentation` private helper.

## New

```lean
universe v u
open scoped CategoryTheory.Obj ZeroObject

attribute [local irreducible] DerivedCategory.monoidalClosed Mod.monoidalClosed
  upperStar lowerStar upperStarFromPoint CondensedRing.upperStarComp upperStarFromPointComp
  Mod.extendScalarsIsoComapInv

open MonoidalCategory MonObj CondensedRing
open CategoryTheory.Pretriangulated
```

The private helper is:

```lean
@[reducible] private noncomputable def stratumPresentation
    {X Z U : Scheme.{u}} [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ Z) [IsOpenImmersion j] : X.FiniteLocallyClosedStratification := by
  let V := j.opensRange
  let S := Scheme.Stratification.ofClosedImmersionOpens i V
  exact
    { n := 3
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := ![(Scheme.openComplementOfIsClosedImmersion i).toScheme, U,
        (Scheme.IdealSheafData.vanishingIdeal ⟨(V : Set Z)ᶜ,
          V.isOpen.isClosed_compl⟩).subscheme]
      immersion a := match a with
        | 0 => (Scheme.openComplementOfIsClosedImmersion i).ι
        | 1 => j ≫ i
        | 2 => V.closedComplement ≫ i
      isImmersion a := by fin_cases a <;> dsimp <;> infer_instance
      range_immersion a := by
        fin_cases a
        · exact S.range_immersion ⟨0, by exact Nat.zero_lt_succ 2⟩
        · change Set.range (j ≫ i) = i '' (V : Set Z)
          simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
            Set.range_comp]
          rfl
        · exact S.range_immersion ⟨2, by exact Nat.lt_succ_self 2⟩ }
```

## Users

The following complete transitive consumer list was produced by
`tools/downstream.py Sheaf.Paper.IntegralTensorShriek --names`. Source searches
for the three public declaration names find no uses outside the item. The direct
importers are `Sheaf.Paper.IntegralTensorProduct`,
`Sheaf.Paper.IntegralTensorPullback`, and
`Sheaf.SixFunctors.IntegralTensorInverseImage`. Their types, definitions, and
inherited public imports are unaffected. No consumer is edited; no adaptation
of a module held by another group is proposed. Consumer claims are not inspected.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralTensorShriek | F2 | Proofs and local elaboration context; original public interface retained. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.DeligneLaumon.GenericDualityModel | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.DeligneLaumon.QbarCurveDuality | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.DeligneLaumon.Reduction.Composition | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.ArithmeticRoots | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.ChernFlagFormula | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.CommonStageFourierWeightUpper | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.CurveIntermediateExtension | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.CurveMiddleExtensionUpper | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.ExceptionalInverseImageExistence | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.ExtensionByZeroPunctual | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.FiniteTorStability | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.FixedStalkIdentificationReduction | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.FlagLocalComparison | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.FlagPullbackInjective | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.FourierTraceFormula | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.GeneralCondensedWeilRealization | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.IntegralDirectImageTower | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.IntegralProperProjectionFormula | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.IntegralTensorProduct | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.IntegralTensorPullback | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.LocalizedFlagProduct | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.LocalizedTopChern | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.ModelCompactComparisonUnit | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.ProjectiveBundleFormula | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.ProperExceptionalRestriction | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.PurityChernClasses | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.QbarMiddleTStructure | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.QbarPerverseSubcategories | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.QbarPerverseSupportCondition | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.RationalPurityPresentation | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.RationalSmoothPurityCanonical | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.SfBidualityClass | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.SmoothProperPurityHypotheses | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.SmoothPullbackSupportDimension | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.SupportedProjectionSplitting | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.TateTwistSupportCondition | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.VectorBundleThomClass | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.WeilFourierInversion | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.WeilFourierPlancherel | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.WeilOne | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Paper.ZlShriekComposition | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SecSmoothPurity.MixedBaseChange | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.CoefQbarVerdier | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.IntegralDualizing | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.IntegralRestrictionLine | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.IntegralVerdier | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.QbarDualRecollement | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.RationalOperations | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SixFunctors.RationalVerdier | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.SmoothPurity.NormalizedWitness | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Targets.PoincareUncurry | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.Targets.SmoothPurityQbar | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| Sheaf.ZetaWeil.WeightPurityRoots | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| TargetsCheck | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.PoincareDuality.Poincare | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.PoincareDuality.Verdier | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.SixFunctors.Adic.Reduction | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.SmoothPurity.Defs | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.Statement | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.TraceFormula.Basic | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.TraceFormula.Slop.Basic | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.TraceFormula.Slop.Correspondence | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.TraceFormula.Slop.Dualizing | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.TraceFormula.Slop.Frobenius | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.TraceFormula.Slop.Main | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.TraceFormula.Slop.Stalk | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.TraceFormula.Statement | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.CohomologicalRange | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.Curve | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.CurveEndpoints | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.EulerProduct | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.FourierPlancherel | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.FourierStalk | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.FourierTrace | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.LFunction | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.LocalizationRational | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.RealPurity | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.VerdierDual | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.ZetaFunction.Examples | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.ZetaFunction.FinalTheorems | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.ZetaFunction.HasseWeil | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.ZetaFunction.IntegralFactors | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.ZetaFunction.LissePurity | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.ZetaFunction.Rationality | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.ZetaFunction.RelativePurity | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.ZetaFunction.SmoothProper | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.ZetaFunction.TraceFormula | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.ZetaFunction.WeightSeparation | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |
| WeilConjectures.ZetaFunction.Weights | not adapted; claim unchanged | Public declaration types, definitions and public imports retained; no edit. |

## Status

landed 20261019T144017-L-2347163 2026-10-19 (merge of deliver/F2/Sheaf.Paper.IntegralTensorShriek)
