# SheafOfModules.ringedTopoiDerivedTensorPullback

## Reason

Retire the unused existence-only predecessor declaration. A whole-library search finds its
name only at its own declaration. The node
lem-weil-pbc-ringed-topoi-derived-tensor-pullback already attaches to
SheafOfModules.ringedTopoiCanonicalDerivedTensorPullback in
Sheaf.Paper.RingedTopoiCanonicalTensorPullback, whose stronger representative square remains
the stated obligation. The direct importer does not invoke the retired theorem.

The module itself remains necessary to forward its public dependencies without changing
its existing importer, Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback. The canonical
module is not a current direct importer. Only this item's declaration is retired; no
module held by another group is edited. The unit record
sk-thm-properbasechange realizes neither the retired theorem nor its module as a unit
statement or proof step.

## Old

```lean
theorem ringedTopoiDerivedTensorPullback
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{u}} {S RI : Sheaf JD CommRingCat.{u}}
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R), uStar.obj M = changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : M ⟶ N), uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))]
    (LF : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)))
    (PR : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ))
    (PS : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ℤ))
    (hPR : ∀ P, PR P ↔ P.IsKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (hPS : ∀ P, PS P ↔ P.IsKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (TR : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    (TS : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
          (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    (rS : (PS.ι.prod PS.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) _
          (SheafOfModules.monoidalCategory S)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PS.ι ⋙ DerivedCategory.Q).prod (PS.ι ⋙ DerivedCategory.Q)) ⋙ TS) :
    (∀ P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ,
      P.IsKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
        CochainComplex.IsKFlat ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ∧
          ∀ n : ℤ,
            (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n).IsFlat) ∧
    Nonempty (TR ⋙ LF ≅ (LF.prod LF) ⋙ TS)
```

## New

The unused theorem has no replacement declaration. Its module keeps precisely its original
public imports and existing module docstring:

```lean
module

public import Sheaf.Paper.RingedTopoiDerivedPullback
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
public import Sheaf.CategoryTheory.RingedSiteModules
```

It has no declarations. The proof-only imports of KFlatResolution, KFlatTelescopeClosure and
ModulePullbackPushforwardAdjunction are removed. All public dependency exports remain the
same. No other Lean module changes; every target statement and definition is unchanged.
Repair of reviewer X-9eb8b point B2: the node's lean.note is restored verbatim to the
reviewed baseline. Retirement is recorded here instead. No other node field changes in
this repair.

## Users

tools/downstream.py reports the following transitive importers. Its --uses query finds no user of ringedTopoiDerivedTensorPullback outside its own module. No target statement or definition is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback | unclaimed | No use of the retired declaration; existing import and all public exports retained. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.Paper.AdicCompletionReduction | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.Paper.FiniteTensorConstructibleCohomology | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | C2 | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.Paper.KoszulQuotientLimit | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.Paper.ProjectionFormulaArrows | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.Paper.ProjectionFormulaFiniteFree | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.Paper.ProjectionFormulaProjectiveSummand | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.Paper.ProjectionFormulaTotalization | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.Paper.RingedExchangeTensorCoherence | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.Paper.RingedTensorSquarePresentation | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.Paper.RingedTopoiCanonicalTensorPullback | U1 | No use of the retired declaration; existing import and all public exports retained. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| TargetsCheck | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationConstructible | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationFiniteTor | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.Statement | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.HomologyShift | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No use of the removed declaration; public dependency exports preserved. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No use of the removed declaration; public dependency exports preserved. |

## Status

landed 20261016T061028-L-328141 2026-10-16 (merge of deliver/V1/Sheaf.Paper.RingedTopoiDerivedTensorPullback)
