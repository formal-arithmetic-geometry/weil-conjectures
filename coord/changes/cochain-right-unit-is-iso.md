# IsIntegralExceptionalSiteDerivedInverse and IsIntegralExceptionalSiteDerivedRight

## Reason

The original concrete normalization predicates repeat derived and cochain functors
on large sheaf categories. Profiling found expensive elaboration of their nested
proofs and kernel checks; a complete proof packet repeatedly exceeded 60 seconds.
Factoring the equations into general predicates avoids expanding those concrete
functors. The factored complete file compiled cleanly in 18.4 seconds on final resumption;
`deliver3.py --no-push` also passed its compilation and preflight. Both original
existence-and-uniqueness holes are proved with no new holes.

## Old

The two normalization definitions were:

```lean
def IsIntegralExceptionalSiteDerivedInverse (n : ℕ)
    (e : (B.derived.level n).inverse ⋙
      (integralExceptionalProRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapDerivedCategory) :
            Prop :=
      ∀ J : CochainComplex (strictEtaleLevel W (integralExceptionalIntegers l E)
        (integralExceptionalUniformizer l E) n) ℤ,
        e.hom.app (DerivedCategory.Q.obj J) ≫
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapDerivedCategory.map
              ((integralExceptionalEtaleRealization l E W n).mapDerivedCategoryFactors.hom.app
                 J) ≫
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
              W).mapDerivedCategoryFactors.hom.app
                (((integralExceptionalEtaleRealization l E W n).mapHomologicalComplex
                   (.up ℤ)).obj J) =
        (integralExceptionalProRealization l E W n).mapDerivedCategory.map
          ((B.derived.level n).inverseFactors.hom.app J) ≫
        (integralExceptionalProRealization l E W n).mapDerivedCategoryFactors.hom.app
          ((((B.ordinary.lift n).modules).mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (integralExceptionalSiteInverse l E W P B n).hom (.up ℤ)).app J)

def IsIntegralExceptionalSiteDerivedRight (n : ℕ)
    (e : (B.derived.level n).direct ⋙
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalProRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor) :
            Prop :=
      ∀ J : CochainComplex (coefficientLevelModules (J := Scheme.ProEt.topology W)
        (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n) ℤ,
        (integralExceptionalEtaleRealization l E W n).mapDerivedCategory.map
          ((B.derived.level n).directUnit.app J) ≫ e.hom.app (DerivedCategory.Q.obj J) ≫
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor.map
          ((integralExceptionalProRealization l E W n).mapDerivedCategoryFactors.hom.app J) =
        (integralExceptionalEtaleRealization l E W n).mapDerivedCategoryFactors.hom.app
          (((B.ordinary.right n).mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (integralExceptionalSiteRight l E W P B n).hom (.up ℤ)).app J) ≫
        integralExceptionalSiteFixedRightUnit l E W n
          (((integralExceptionalProRealization l E W n).mapHomologicalComplex
             (.up ℤ)).obj J)
```

The file opened `CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
SheafOfModules`. There were no private proof helpers or local proof attributes.

## New

The two definitions retain their signatures and now specialize these general
normalization formulas:

```lean
def CategoryTheory.Functor.IsDerivedInverseComparison
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) [F.Additive]
    (R : B ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (S : A ⥤ C) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (T : C ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (V : DerivedCategory A ⥤ DerivedCategory B)
    (factors : DerivedCategory.Q ⋙ V ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (comparison : F ⋙ R ≅ S ⋙ T)
    (e : V ⋙ R.mapDerivedCategory ≅ S.mapDerivedCategory ⋙ T.mapDerivedCategory) : Prop :=
    ∀ J : CochainComplex A ℤ,
        e.hom.app (DerivedCategory.Q.obj J) ≫
            T.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app J) ≫
            T.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj J) =
          R.mapDerivedCategory.map (factors.hom.app J) ≫
            R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex comparison.hom (.up ℤ)).app J)

def CategoryTheory.Functor.IsDerivedRightComparison
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions D]
    (G : B ⥤ A) [G.Additive] (R : B ⥤ D) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (S : A ⥤ C) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (T : D ⥤ C) [T.Additive] (V : DerivedCategory B ⥤ DerivedCategory A)
    (vunit : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ V)
    (comparison : G ⋙ S ≅ R ⋙ T)
    (e : V ⋙ S.mapDerivedCategory ≅ R.mapDerivedCategory ⋙ T.rightDerivedFunctor) : Prop :=
    ∀ J : CochainComplex B ℤ,
        S.mapDerivedCategory.map (vunit.app J) ≫ e.hom.app (DerivedCategory.Q.obj J) ≫
            T.rightDerivedFunctor.map (R.mapDerivedCategoryFactors.hom.app J) =
          S.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex comparison.hom (.up ℤ)).app J) ≫
            ((DerivedCategory.quotientCompQhIso C).inv.app _ ≫
              T.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient D (.up ℤ)).obj
                ((R.mapHomologicalComplex (.up ℤ)).obj J)) ≫
              T.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso D).inv.app
                ((R.mapHomologicalComplex (.up ℤ)).obj J)))

def IsIntegralExceptionalSiteDerivedInverse (n : ℕ)
    (e : (B.derived.level n).inverse ⋙
      (integralExceptionalProRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).mapDerivedCategory) :
            Prop :=
  CategoryTheory.Functor.IsDerivedInverseComparison (B.ordinary.lift n).modules
    (integralExceptionalProRealization l E W n) (integralExceptionalEtaleRealization l E W n)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W)
    (B.derived.level n).inverse (B.derived.level n).inverseFactors
    (integralExceptionalSiteInverse l E W P B n) e

def IsIntegralExceptionalSiteDerivedRight (n : ℕ)
    (e : (B.derived.level n).direct ⋙
      (integralExceptionalEtaleRealization l E W n).mapDerivedCategory ≅
      (integralExceptionalProRealization l E W n).mapDerivedCategory ⋙
        (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W).rightDerivedFunctor) :
            Prop :=
  CategoryTheory.Functor.IsDerivedRightComparison (B.ordinary.right n)
    (integralExceptionalProRealization l E W n) (integralExceptionalEtaleRealization l E W n)
    (ProEtale.comparisonLowerStar (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) W)
    (B.derived.level n).direct (B.derived.level n).directUnit
    (integralExceptionalSiteRight l E W P B n) e
```

Expanding the general predicates gives precisely the previous equations; the
cochain complexes, ordinary comparisons, derived units, and all factorization
maps have the same orientation. The old and new equations were compared directly, including the component
formulas of the fixed right unit. A separate concrete normalization probe was
attempted but timed out; it is not counted as successful validation. The
unchanged direct consumer compiled against the sandbox module in 26.5 seconds. The fixed right unit and both chosen comparison
definitions are unchanged. Thus no target or consumer changes meaning.

The proof additionally opens `CategoryTheory.Functor` and uses these file-local
attributes, after proving the private cochain unit API:

```lean
attribute [local instance] cochainRightUnit_isIso
attribute [local irreducible] WeilConjectures.integralExceptionalProRealization
  WeilConjectures.integralExceptionalEtaleRealization
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
```

No instance or reducibility attribute is exported. All private helpers are proved.
The sole new proof import is
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
No existing public import, signature, visibility or docstring changes.

## Users

The source import graph has one direct consumer,
`Sheaf.Paper.AdicPurityExceptionalReduction`. `tools/downstream.py` lists the following
142 transitive consumers. Their existing declarations keep exactly the same
meaning: the two predicates are definitionally equal to the old formulas, the two
specifications are now proved, and all new attributes are local. No consumer is
adapted or claimed. A source search finds no external use of either normalization
predicate; the direct consumer uses the chosen comparison isomorphisms.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.PurityChernClasses | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.WeilOne | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| TargetsCheck | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.Statement | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | Not queried; unchanged | Same signatures and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | Not queried; unchanged | Same signatures and meaning; no adaptation. |

## Status

landed 20261019T192856-L-1879286 2026-10-19 (merge of deliver/Z5/Sheaf.Paper.ExceptionalDerivedSiteRealization)
