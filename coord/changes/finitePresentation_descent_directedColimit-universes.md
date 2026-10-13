# ModuleCat.finitePresentation_descent_directedColimit

## Reason

The original Lean independently generalizes hidden module universes. In the object clause the final module is in max(u,v) but the requested stage model is in v, which need not contain the ring universe u. A constant directed diagram of a field whose cardinality exceeds that of any Type v carrier has no nonzero Type v module, whereas its regular module is finitely presented. Explicit module universes max(u,v), max(u,w), max(u,z) repair this source-mismatched size constraint. Ring, index, and all algebraic hypotheses and conclusions are unchanged.

Only this intermediate declaration changes. No Challenge target signature or definition changes. The concrete ULift quotient supplies stage data without any exported definition choosing an unspecified witness. The map and equality clauses use the independently sized common module categories needed by the extension-restriction adjunction and its composition comparison.

## Old

```lean
theorem finitePresentation_descent_directedColimit
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat) :
    (∀ (N : ModuleCat (colimit F : CommRingCat)),
      Module.FinitePresentation (colimit F : CommRingCat) N →
      ∃ (i : I) (M : ModuleCat (F.obj i)), Module.FinitePresentation (F.obj i) M ∧
        Nonempty ((extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj M ≅ N)) ∧
    (∀ (i : I) (M N : ModuleCat (F.obj i)),
      Module.FinitePresentation (F.obj i) M →
      Module.FinitePresentation (F.obj i) N →
      ∀ (f : (extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj M ⟶
          (extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj N),
        ∃ (j : I) (hij : i ≤ j),
          let rij := CommRingCat.Hom.hom (F.map (homOfLE hij))
          let rj := CommRingCat.Hom.hom (colimit.ι F j)
          let ri := CommRingCat.Hom.hom (colimit.ι F i)
          ∃ (g : (extendScalars rij).obj M ⟶ (extendScalars rij).obj N)
            (eM : (extendScalars ri).obj M ≅
              (extendScalars rj).obj ((extendScalars rij).obj M))
            (eN : (extendScalars ri).obj N ≅
              (extendScalars rj).obj ((extendScalars rij).obj N)),
            (∀ m : M,
              eM.hom ((1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj i, ri] m) =
                (1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj j, rj]
                  ((1 : ↑(F.obj j)) ⊗ₜ[F.obj i, rij] m)) ∧
            (∀ n : N,
              eN.hom ((1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj i, ri] n) =
                (1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj j, rj]
                  ((1 : ↑(F.obj j)) ⊗ₜ[F.obj i, rij] n)) ∧
            f ≫ eN.hom = eM.hom ≫ (extendScalars rj).map g) ∧
    (∀ (i : I) (M N : ModuleCat (F.obj i)),
      Module.FinitePresentation (F.obj i) M →
      Module.FinitePresentation (F.obj i) N →
      ∀ (f g : M ⟶ N),
        (extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).map f =
          (extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).map g →
        ∃ (j : I) (hij : i ≤ j),
          (extendScalars (CommRingCat.Hom.hom (F.map (homOfLE hij)))).map f =
            (extendScalars (CommRingCat.Hom.hom (F.map (homOfLE hij)))).map g)
```

## New

```lean
theorem finitePresentation_descent_directedColimit
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat) :
    (∀ (N : ModuleCat.{max u v} (colimit F : CommRingCat)),
      Module.FinitePresentation (colimit F : CommRingCat) N →
      ∃ (i : I) (M : ModuleCat.{max u v} (F.obj i)), Module.FinitePresentation (F.obj i) M ∧
        Nonempty ((extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj M ≅ N)) ∧
    (∀ (i : I) (M N : ModuleCat.{max u w} (F.obj i)),
      Module.FinitePresentation (F.obj i) M →
      Module.FinitePresentation (F.obj i) N →
      ∀ (f : (extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj M ⟶
          (extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj N),
        ∃ (j : I) (hij : i ≤ j),
          let rij := CommRingCat.Hom.hom (F.map (homOfLE hij))
          let rj := CommRingCat.Hom.hom (colimit.ι F j)
          let ri := CommRingCat.Hom.hom (colimit.ι F i)
          ∃ (g : (extendScalars rij).obj M ⟶ (extendScalars rij).obj N)
            (eM : (extendScalars ri).obj M ≅
              (extendScalars rj).obj ((extendScalars rij).obj M))
            (eN : (extendScalars ri).obj N ≅
              (extendScalars rj).obj ((extendScalars rij).obj N)),
            (∀ m : M,
              eM.hom ((1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj i, ri] m) =
                (1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj j, rj]
                  ((1 : ↑(F.obj j)) ⊗ₜ[F.obj i, rij] m)) ∧
            (∀ n : N,
              eN.hom ((1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj i, ri] n) =
                (1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj j, rj]
                  ((1 : ↑(F.obj j)) ⊗ₜ[F.obj i, rij] n)) ∧
            f ≫ eN.hom = eM.hom ≫ (extendScalars rj).map g) ∧
    (∀ (i : I) (M N : ModuleCat.{max u z} (F.obj i)),
      Module.FinitePresentation (F.obj i) M →
      Module.FinitePresentation (F.obj i) N →
      ∀ (f g : M ⟶ N),
        (extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).map f =
          (extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).map g →
        ∃ (j : I) (hij : i ≤ j),
          (extendScalars (CommRingCat.Hom.hom (F.map (homOfLE hij)))).map f =
            (extendScalars (CommRingCat.Hom.hom (F.map (homOfLE hij)))).map g)
```

## Users

The downstream tool lists the following transitive import dependents. Its --uses search and a repository-wide declaration-name search find no application outside the item itself. Their declarations therefore do not change meaning, and no adapted module is delivered. All seven unchanged direct importers compile against the changed module. The largest initially timed out, then passed the overlay recheck in 53.1 seconds; its baseline took 11.8 seconds. No forced source adaptation is necessary.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.AffineDifferentialColimitDescent | X2 | Import only; no theorem application; no adaptation. |
| Sheaf.Algebra.Homology.AffinePerfectChainMapDescent | N4 | Import only; no theorem application; no adaptation. |
| Sheaf.Algebra.Homology.AffinePerfectColimitDescent | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.Algebra.Homology.AffinePerfectHomotopyDescent | V1 | Import only; no theorem application; no adaptation. |
| Sheaf.Algebra.Homology.FiniteProjectiveGradedColimitDescent | W3 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineFlatModuleDescent | T4 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.AffinePerfectHomColimit | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | G1 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedFreeStalkComplexLift | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedFreeStalkComplexLocalLift | K3 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedFreeStalkModelSpread | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.FilteredCartesianFlatComplexDescent | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.FilteredCartesianPerfectDescent | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFlatProperSupportDescent | W4 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePresentationModuleMapDescent | H3 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRelationDescent | P2 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitelyPresentedComplexDescent | X3 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatBoundedComplexDescent | S2 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatModuleDescent | C2 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectComplexDescent | K4 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectCutComplexDegreeZero | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDescendMorphisms | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModelExistence | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectHomContinuity | C2 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLocalDegreeZeroUnit | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectStalkDerivedHomLift | M3 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectStalkDerivedIsoSpread | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectStalkQuasiIsoDetection | M3 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectUniversalH0BottomModel | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectUniversalH0LocalChainModel | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectUniversalH0TruncationPullback | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectUniversalLowestCohomologyPullback | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectUniversalLowestZeroModel | M3 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | V3 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization | S2 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | X2 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchResidueCriterion | Q4 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | V1 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect | S1 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | P4 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | T4 | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Import only; no theorem application; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Import only; no theorem application; no adaptation. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Import only; no theorem application; no adaptation. |
| TargetsCheck | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Import only; no theorem application; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Import only; no theorem application; no adaptation. |

## Status

landed 20261013T100207-L-2499385 2026-10-13 (merge of deliver/V4/Sheaf.Algebra.FinitePresentationColimit)
