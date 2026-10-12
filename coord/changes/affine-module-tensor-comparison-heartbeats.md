# AlgebraicGeometry.Scheme.Modules.affine_module_tensor_comparison_isIso

## Reason

Preflight treats a declaration-scoped option wrapper as an interface command change and
requires a change record. The option only increases proof elaboration heartbeats from
200000 to 400000. The new proof compares the definitionally equal scalar-restricted
pushforward and scheme pushforward in the adjunction triangle calculation. It compiles
within the 60-second file limit (about 35 seconds). A tactic-local option did not raise
the declaration's outer heartbeat budget. This record is for that elaboration setting;
no definition or theorem statement changes, and no module requires adaptation or a claim.

## Old

```lean
theorem affine_module_tensor_comparison_isIso [IsAffineHom f]
     (B : U.toTopCat.Sheaf CommRingCat.{u})
      (b : U.sheaf ⟶ B) (t : IA ⟶ B) (ε : B ⟶ U.sheaf)
    (hring : IsPushout r₀ t₀ b t ∧ b ≫ ε = 𝟙 U.sheaf ∧ t ≫ ε = e₀)
     (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
        (pobj : ∀ G, P.obj G = SheafOfModules.changeOfRings.{u, u, u} t (I G))
        (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f)
    (hP : (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
          P.map a = eqToHom (pobj G) ≫
            SheafOfModules.changeOfRingsHom.{u, u, u} t (I G)
              (TopCat.Sheaf.inverseImageModuleMap f.base A G a) ≫
            eqToHom (pobj G').symm) ∧
        (∀ (G : SheafOfModules.{u} (𝓡 A)) (V : (Opens X)ᵒᵖ) (g : G.val.obj V),
          ((eqToHom (pobj G)).val.app (fV V))
            ((κ.inv.app G).val.app (fV V)
              (((adj₀).unit.app ((S).obj G)).val.app V g)) =
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
              (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t (I G))).app
                (fV V)
                ((1 : B.obj.obj (fV V)) ⊗ₜ[(IA).obj.obj (fV V),(t.hom.app (fV V)).hom]
                  (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                    (Opens.map f.base) AddCommGrpCat.{u} (𝓙 X) (𝓙 U)).unit.app
                      ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g))))
     (H : SheafOfModules.{u} (𝓡 A) ⥤ U.Modules)
          (hobj : ∀ G, H.obj G = SheafOfModules.changeOfRings.{u, u, u} ε (P.obj G))
          (γ : S ⋙ tensorPullback f ⟶ H)
    (hH : (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
            H.map a = eqToHom (hobj G) ≫
              SheafOfModules.changeOfRingsHom.{u, u, u} ε (P.obj G) (P.map a) ≫
              eqToHom (hobj G').symm) ∧
          (∀ (G : SheafOfModules.{u} (𝓡 A)) (W : (Opens U)ᵒᵖ)
              (p : (P.obj G).val.obj W),
            ((eqToHom (hobj G)).val.app W)
              ((γ.app G).val.app W ((κ.hom.app G).val.app W p)) =
              ((PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
                (SheafOfModules.changeOfRingsPresheaf.{u, u, u} ε (P.obj G))).app W
                  ((1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W,(ε.hom.app W).hom] p)) ∧
          (∀ G : SheafOfModules.{u} (𝓡 A),
            G.IsQuasicoherent → (H.obj G).IsQuasicoherent))
     (α : R ⋙ H ⟶ 𝟭 U.Modules) (β : 𝟭 (SheafOfModules.{u} (𝓡 A)) ⟶ H ⋙ R)
    (hcomp : (∀ F : U.Modules, γ.app ((R).obj F) ≫ α.app F = (adj₀).counit.app F) ∧
            (∀ G : SheafOfModules.{u} (𝓡 A),
              (S).map (β.app G) = ((adj₀).homEquiv ((S).obj G) (H.obj G)) (γ.app G))) :
(∀ F : U.Modules, F.IsQuasicoherent → IsIso (α.app F)) ∧
            (∀ G : SheafOfModules.{u} (𝓡 A), G.IsQuasicoherent → IsIso (β.app G))
```

## New

```lean
set_option maxHeartbeats 400000 in
-- The adjunction identity compares two definitionally equal scalar-restricted pushforwards.
theorem affine_module_tensor_comparison_isIso [IsAffineHom f]
     (B : U.toTopCat.Sheaf CommRingCat.{u})
      (b : U.sheaf ⟶ B) (t : IA ⟶ B) (ε : B ⟶ U.sheaf)
    (hring : IsPushout r₀ t₀ b t ∧ b ≫ ε = 𝟙 U.sheaf ∧ t ≫ ε = e₀)
     (P : SheafOfModules.{u} (𝓡 A) ⥤ SheafOfModules.{u} (𝓡 B))
        (pobj : ∀ G, P.obj G = SheafOfModules.changeOfRings.{u, u, u} t (I G))
        (κ : P ⋙ SheafOfModules.restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f)
    (hP : (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
          P.map a = eqToHom (pobj G) ≫
            SheafOfModules.changeOfRingsHom.{u, u, u} t (I G)
              (TopCat.Sheaf.inverseImageModuleMap f.base A G a) ≫
            eqToHom (pobj G').symm) ∧
        (∀ (G : SheafOfModules.{u} (𝓡 A)) (V : (Opens X)ᵒᵖ) (g : G.val.obj V),
          ((eqToHom (pobj G)).val.app (fV V))
            ((κ.inv.app G).val.app (fV V)
              (((adj₀).unit.app ((S).obj G)).val.app V g)) =
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
              (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t (I G))).app
                (fV V)
                ((1 : B.obj.obj (fV V)) ⊗ₜ[(IA).obj.obj (fV V),(t.hom.app (fV V)).hom]
                  (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                    (Opens.map f.base) AddCommGrpCat.{u} (𝓙 X) (𝓙 U)).unit.app
                      ((SheafOfModules.toSheaf (𝓡 A)).obj G)).hom.app V g))))
     (H : SheafOfModules.{u} (𝓡 A) ⥤ U.Modules)
          (hobj : ∀ G, H.obj G = SheafOfModules.changeOfRings.{u, u, u} ε (P.obj G))
          (γ : S ⋙ tensorPullback f ⟶ H)
    (hH : (∀ (G G' : SheafOfModules.{u} (𝓡 A)) (a : G ⟶ G'),
            H.map a = eqToHom (hobj G) ≫
              SheafOfModules.changeOfRingsHom.{u, u, u} ε (P.obj G) (P.map a) ≫
              eqToHom (hobj G').symm) ∧
          (∀ (G : SheafOfModules.{u} (𝓡 A)) (W : (Opens U)ᵒᵖ)
              (p : (P.obj G).val.obj W),
            ((eqToHom (hobj G)).val.app W)
              ((γ.app G).val.app W ((κ.hom.app G).val.app W p)) =
              ((PresheafOfModules.sheafificationAdjunction (𝟙 U.ringCatSheaf.obj)).unit.app
                (SheafOfModules.changeOfRingsPresheaf.{u, u, u} ε (P.obj G))).app W
                  ((1 : U.sheaf.obj.obj W) ⊗ₜ[B.obj.obj W,(ε.hom.app W).hom] p)) ∧
          (∀ G : SheafOfModules.{u} (𝓡 A),
            G.IsQuasicoherent → (H.obj G).IsQuasicoherent))
     (α : R ⋙ H ⟶ 𝟭 U.Modules) (β : 𝟭 (SheafOfModules.{u} (𝓡 A)) ⟶ H ⋙ R)
    (hcomp : (∀ F : U.Modules, γ.app ((R).obj F) ≫ α.app F = (adj₀).counit.app F) ∧
            (∀ G : SheafOfModules.{u} (𝓡 A),
              (S).map (β.app G) = ((adj₀).homEquiv ((S).obj G) (H.obj G)) (γ.app G))) :
(∀ F : U.Modules, F.IsQuasicoherent → IsIso (α.app F)) ∧
            (∀ G : SheafOfModules.{u} (𝓡 A), G.IsQuasicoherent → IsIso (β.app G))
```

The displayed signature is byte-for-byte unchanged. Only the proof and its elaboration
budget differ. The wrapper's scope ends with this theorem, so importers inherit no option.
Every target retains exactly its previous elaborated type; no statement review reopens.

## Users

Ran tools/downstream.py with --uses affine_module_tensor_comparison_isIso: the only direct
textual user besides the declaration itself is Sheaf.AlgebraicGeometry.AffineModuleCorrespondence,
whose call needs no change. All transitive importers from tools/downstream.py --names are
listed below; each receives the same declaration type and public imports. None is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineModuleTensorComparisonIsIso | X2 | Proof elaboration budget only. |
| Sheaf.AlgebraicGeometry.AffineAlgebraDerivedAdjunctionIsos | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.AffineAlgebraDerivedAdjunctionQCoh | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.AffineAlgebraTensorPullbackExact | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.AffineDerivedConcentration | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.AffineDerivedHomEvaluationCounit | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.AffineDerivedHomLocalizedEvaluation | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.AffineDerivedPushforwardConservative | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.AffineDerivedPushforwardTExact | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.AffineModuleCorrespondence | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.AffineModuleFiniteType | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.CohomologyPowersIdealApplication | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.CohomologyPowersIdealReesFinite | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FibreCartierLocal | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FiniteAffineAdjointCounitComparison | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FiniteAffineDerivedEquivalence | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FiniteAffineDerivedFactorization | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FiniteDualityDegreeZeroCounitAction | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FiniteDualityDerivedHom | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FiniteFlatDualityEvaluation | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FiniteRestrictionDerivedRightAdjoint | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FiniteScalarRightAdjointQCoh | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FiniteSheafHomAffineAdjoint | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FiniteTwistedInverseBoundedBelow | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FormalCompletionFullyFaithfulProper | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FormalFunctionsCompleteBase | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteFibreVanishing | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FormalFunctionsStalk | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPull | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.GradedSerreVanishing | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProjective | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProper | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedHom | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedSystem | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSystemSupport | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionAlgebraDual | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorPullback | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.ProperFibreIdempotentImage | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.ProperNormalizedFibres | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.TheoremFormalFunctions | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier | unchanged | No effect; same theorem type and public imports. |
| Sheaf.AlgebraicGeometry.VanishingProjective | unchanged | No effect; same theorem type and public imports. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unchanged | No effect; same theorem type and public imports. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unchanged | No effect; same theorem type and public imports. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unchanged | No effect; same theorem type and public imports. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unchanged | No effect; same theorem type and public imports. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unchanged | No effect; same theorem type and public imports. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unchanged | No effect; same theorem type and public imports. |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unchanged | No effect; same theorem type and public imports. |
| Sheaf.Paper.GaloisLisseRepresentations | unchanged | No effect; same theorem type and public imports. |
| Sheaf.Paper.GradedFinitenessCohomology | unchanged | No effect; same theorem type and public imports. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unchanged | No effect; same theorem type and public imports. |
| Sheaf.Paper.MLCohomologyPowersIdeal | unchanged | No effect; same theorem type and public imports. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unchanged | No effect; same theorem type and public imports. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unchanged | No effect; same theorem type and public imports. |
| TargetsCheck | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.FourierTransform.AffineSpace | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.FourierTransform.Defs | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.FourierTransform.Inversion | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.FourierTransform.Perverse | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.FourierTransform.Properties | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.FourierTransform.Properties.Stalk | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Gabber | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unchanged | No effect; same theorem type and public imports. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unchanged | No effect; same theorem type and public imports. |

## Status

landed 20261012T135333-L-1699990 2026-10-12 (merge of deliver/X2/Sheaf.AlgebraicGeometry.AffineModuleTensorComparisonIsIso)
