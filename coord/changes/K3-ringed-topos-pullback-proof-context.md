# SheafOfModules.isKFlat_ringedToposPullback

## Reason

The returned delivery also contained two identical private proofs of
`SheafOfModules.tensorLeft_additive_independent`, one in the item and one in the
new bounded-flat module. The repair moves the one proved declaration into the new
tensor-colimit module, public, and removes both private consumer copies. Both
consumers already directly import that module, so neither imports nor public
interfaces of existing library declarations change. This is shared proof
infrastructure within the existing delivered nodes, not a changed statement.

The static stage-3 preflight reports an interface-context change because the proof file
adds `open CategoryTheory.Functor MonoidalCategory` and a `variable` block inside
`namespace SheafOfModules`. These commands support private proof helpers. Existing
public declaration signatures and all public imports are byte-for-byte identical.
The theorem's own binders explicitly specify the site, coefficient and functor data;
the added variable block does not add or change any binder. The namespace closes at
the end of the module. No definition or target changes and no forced adaptation occurs.

## Old

```lean
theorem isKFlat_ringedToposPullback
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{w}} {S RI : Sheaf JD CommRingCat.{w}}
    (uInv : Sheaf JC (Type (w)) ⥤ Sheaf JD (Type (w)))
    (uPush : Sheaf JD (Type (w)) ⥤ Sheaf JC (Type (w)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤
      ringedSiteModules.{w} ((sheafCompose JD
        (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (hobj : ∀ M : ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R),
      uStar.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)} (a : M ⟶ N),
      uStar.map a = eqToHom (hobj M) ≫
        changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫ eqToHom (hobj N).symm)
    [uStar.Additive]
    (P : CochainComplex (ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hflat : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients
      ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ∧
      ∀ n : ℤ, IsFlatOnSite (J := JD) (R := S)
        (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n)
```

Original context: `universe uC vC uD vD w`,
`open CategoryTheory CategoryTheory.Limits`, `namespace SheafOfModules`.

## New

```lean
theorem isKFlat_ringedToposPullback
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{w}} {S RI : Sheaf JD CommRingCat.{w}}
    (uInv : Sheaf JC (Type (w)) ⥤ Sheaf JD (Type (w)))
    (uPush : Sheaf JD (Type (w)) ⥤ Sheaf JC (Type (w)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤
      ringedSiteModules.{w} ((sheafCompose JD
        (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (hobj : ∀ M : ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R),
      uStar.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)} (a : M ⟶ N),
      uStar.map a = eqToHom (hobj M) ≫
        changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫ eqToHom (hobj N).symm)
    [uStar.Additive]
    (P : CochainComplex (ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hflat : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients
      ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ∧
      ∀ n : ℤ, IsFlatOnSite (J := JD) (R := S)
        (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n)
```

Additional proof context inside the same namespace:

```lean
open CategoryTheory.Functor MonoidalCategory

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  {R : Sheaf JC CommRingCat.{w}} {RI : Sheaf JD CommRingCat.{w}}
  {L : Sheaf JC (Type w) ⥤ Sheaf JD (Type w)}
```

## Users

A source scan found 503 transitive project importers. The only
external module mentioning the declaration in executable Lean is
`Sheaf.Paper.RingedTopoiDerivedPullback`; its existing application has the identical
signature available. `RingedPullbackPreservesKFlat` mentions it only in documentation.
The table includes all transitive project importers, conservatively. None is edited.
The standard `tools/downstream.py --uses` subsequently completed after waiting for
the shared index lock. It reports 502 importers in the configured library roots and
exactly the same executable declaration user. The conservative source scan additionally
includes `Comparator.Weil.Solution`, hence the 503-row importer list here.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.KFlatRingedToposPullback` | K3 | Proof replaced; original signature identical. |
| `Comparator.Weil.Solution` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.Algebra.Homology.DiagramKFlatReplacements` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.AffineCurveCohomologicalDimension` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.AffineSupportVanishing` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.CompactBoundedConstructibleBaseChange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ConstantFiniteComparison` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ConstructibleFiniteSurjectionCancellation` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImagesComp` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ConstructibleModificationTransfer` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportBaseChangeQcqs` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.FiniteBoundaryComparison` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.FiniteBoundaryReconstruction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.GeometricFiberFinite` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.IntegralSurjectiveTargetBaseChange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.LerayBounded` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ModificationExtensionZero` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.OpenDirectImageOverField` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteObjectwise` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProjectiveCurveConstant` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroup` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineConstructible` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProjectiveSmoothCurveFiniteness` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProperBoundedConstructible` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProperCaseConstructibility` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProperConstructibleHigherDirectImages` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProperOpenComparisonComposition` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProperOpenComparisonIso` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProperProjectionFormula` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.RelativeDimensionOneInduction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimensionGroundField` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.SmoothGenericDirectImage` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.SmoothTensorDuality` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.TorsionSheafProperBaseChange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison` | F4 | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.UnboundedCoefficientForgetfulAux` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.UniversalBaseChangeFailureDatum` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.AlgebraicGeometry.UniversalCurveTestVanishing` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition` | H4 | No edit or adaptation; signature and public imports identical. |
| `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.Paper.AdicCompletionReduction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.Paper.FiniteTensorConstructibleCohomology` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.Paper.IntegralExchangeReduction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.Paper.IntegralFiniteExchangeComparison` | C2 | No edit or adaptation; signature and public imports identical. |
| `Sheaf.Paper.KoszulQuotientLimit` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.Paper.OpenCurveEtaleLerayLowDegree` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.Paper.ProjectionFormulaArrows` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.Paper.ProjectionFormulaFiniteFree` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.Paper.ProjectionFormulaProjectiveSummand` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.Paper.ProjectionFormulaTotalization` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.Paper.RingedExchangeTensorCoherence` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.Paper.RingedPullbackPreservesKFlat` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.Paper.RingedTensorSquarePresentation` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.Paper.RingedTopoiCanonicalTensorPullback` | U1 | No edit or adaptation; signature and public imports identical. |
| `Sheaf.Paper.RingedTopoiDerivedPullback` | unclaimed | Calls the original theorem unchanged; no edit or adaptation. |
| `Sheaf.Paper.RingedTopoiDerivedTensorPullback` | V1 | No edit or adaptation; signature and public imports identical. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.WeilSheaf.AffineCurveRangePositive` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.WeilSheaf.CohomologyGeometricConjugacy` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.WeilSheaf.CohomologyGeometricEquivalence` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `Sheaf.WeilSheaf.FiniteBoundaryPositive` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `TargetsCheck` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.Defs` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.DenseOpen` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.DeligneLaumon.Reduction.Weights` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Pairing` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Transport` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Adic` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceAdjunction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceTrace` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Basic` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicallySmooth` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.FamilyObject` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.FrameIndependence` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductAppend` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Rational` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.ShiftTateObjectAssoc` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClass` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Trace` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.TateTwist.Basic` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.TateTwist.KummerClass` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.EtaleCohomology.TateTwist.Normalized` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.FourierTransform.AffineSpace` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.FourierTransform.AffineSpace.ArtinSchreierVanishing` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.FourierTransform.AffineSpace.Convolution` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.FourierTransform.AffineSpace.KernelTransform` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.FourierTransform.AffineSpace.Transform` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.FourierTransform.AffineSpace.Unit` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.FourierTransform.AffineSpace.UnitVanishing` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.FourierTransform.ArtinSchreierCohomology` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.FourierTransform.Composition` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.FourierTransform.Defs` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.FourierTransform.Inversion` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.FourierTransform.Properties` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.FourierTransform.Properties.BaseChange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.FourierTransform.Properties.BaseLinear` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.FourierTransform.Properties.Stalk` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Composition` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Dualizing` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupportBaseChange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteBoundary` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteComparison` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Kunneth` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Modification` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Projective` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.TargetLocal` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ClosedImmersion` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryCompactSupport` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryProper` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Localization` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocallyConstantInvertible` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekReduction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Orientation` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Package` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Perfect` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Perfect.TateTwist` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Point` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.RationalStage` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Shift` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.ShiftAssoc` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.SingleDelta` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.TorSheaf` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Supports` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.SupportsBaseChange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.SupportsEtale` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.SupportsOpenImmersion` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.TensorHom` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.Triangulated` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek` | XRdbb7091a3d1839f4 | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsComposition` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekOpenRestriction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Pairing` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplex` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Basic` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Adic.Localization` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.DualPerfect` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Duality` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Finiteness` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.HomComparison` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationConstructible` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationFiniteTor` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekBaseChange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekIndependence` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Perfect` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormula` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormulaExtendScalars` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ScalarExtension` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Stability` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.ScalarExtension` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Additivity` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Adic` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobenius` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusLift` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusTrace` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicRange` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicSystem` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineLine` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineReduction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Curve` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Defs` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.FiniteModel` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.FixedPoints` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.GlobalOperator` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Iterate` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.KernelPushforward` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.LocalFrobenius` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Localization` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Main` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.ModelRestriction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.Perfectness` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperCurve` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperPushforward` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardFibres` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardStep` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.RelativeAffineLine` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceClass` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceFormulaHolds` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceMap` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.SixFunctors.ProEtale.WeaklyContractibleCohomology` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.Statement` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.ArtinSchreierDual` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.ArtinSchreierFrobenius` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.ArtinSchreierPurity` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.ArtinSchreierTrace` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.BoundaryStalk` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.Cohomology` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.CohomologyExact` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.CohomologyShift` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.ComplexWeights` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.ConstantTwistCohomology` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.Defs` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.DenseOpen` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.DirectImageRestriction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.DirectImageStalk` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.ExtensionByZero` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.FiniteEtaleLisse` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.Finiteness` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.Fourier` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.FourierInversion` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.FourierInversion.Defs` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.FourierInversion.TensorLisse` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.FourierInversion.UpperStar` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.FourierInversion.Vanishing` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.FourierPlancherel` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.FourierTateTwist` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.FourierTateTwist.Transform` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.FourierTrace` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.FourierTraceAux` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.GeometricCoinvariants` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.GeometricallyConstant` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.GrothendieckLefschetz` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.HomologyShift` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.Localization` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.LocalizationRational` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.LowerShriek` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.LowerStar` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.LowerStarComp` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.LowerStarId` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.LowerStarPairing` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.LowerStarTensorPow` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.MiddleExtension` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.OpenImmersion` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.OpenImmersionRestriction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.Operations` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.PoincareDuality` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.ProperCohomology` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.Realizable` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.StalkConstantTwist` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.StalkExtensionByZero` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.StalkInternalHom` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.StalkOpenImmersion` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.StalkTateTwist` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.StalkTensor` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.TateTwist` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.TateTwistCohomology` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.Tensor` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.TensorObjPairing` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.TensorPower` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.TraceFunctionCongr` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.TraceFunctionOps` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.TraceFunctionTensor` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.TraceSeries` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.WeilSheaf.UpperStarPointwise` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.ZetaFunction.SixOperations` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | No edit or adaptation; signature and public imports identical. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | No edit or adaptation; signature and public imports identical. |

## Status

landed 20261016T064223-L-582607 2026-10-16 (merge of deliver/K3/Sheaf.Paper.KFlatRingedToposPullback)
