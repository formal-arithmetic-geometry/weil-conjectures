# CategoryTheory.ringedToposDerivedPushforwardComposition

## Reason

The theorem's inferred universe and site arguments caused elaboration to exceed the
single-file time limit before its proof was checked. Explicitly supply the existing
coefficient universe `u` on `CommRingCat` and `RingCat`, and the existing site parameters
on the two `RingedToposMorphism` arguments. These are elaboration annotations only:
no binder, hypothesis, conclusion, or universe parameter is added or removed. All
these parameters were already determined by the surrounding ring sheaves and sites.
The resulting theorem has the same kernel type. No definition changes.

Second-reading verification: exported the original compiled declaration type as an
expression graph, reconstructed it without re-elaborating the slow written signature,
and submitted a theorem of that type with the delivered declaration as its proof to
`Lean.addDecl`. Lean's kernel accepted it. Both declarations have universe parameters
`[u, w]`. Their raw types differ only in inferred proof terms for universe-size
propositions, which are definitionally equal by proof irrelevance. The scratch probe
printed `KERNEL SIGNATURE COMPATIBILITY PASSED`.

The proof uses private generic helpers and additional local universe names. The
backward elaboration options are local to this module. All original public imports
and all existing declaration visibility are preserved.

## Old

```lean
theorem ringedToposDerivedPushforwardComposition
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E)
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (R : Sheaf L CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat
      RingCat)).obj
      A))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat
      RingCat)).obj
      B))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose L (forget₂ CommRingCat
      RingCat)).obj
      R))]
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (g : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)
      ((sheafCompose L (forget₂ CommRingCat RingCat)).obj R)) :
    ∃ (Rf : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
      CommRingCat
      RingCat)).obj
      A)) ⥤
          DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat
            RingCat)).obj
            B)))
      (Rg : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂
        CommRingCat
        RingCat)).obj
        B)) ⥤
          DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose L (forget₂ CommRingCat
            RingCat)).obj
            R)))
      (Rgf : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
        CommRingCat
        RingCat)).obj A)) ⥤
          DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose L (forget₂ CommRingCat
            RingCat)).obj
            R)))
      (ηf : f.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ Rf)
      (ηg : g.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ Rg)
      (ηgf : (f.modules ⋙ g.modules).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ Rgf),
      Rf.IsRightDerivedFunctor ηf
          (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
            CommRingCat
            RingCat)).obj A)) (ComplexShape.up ℤ)) ∧
      Rg.IsRightDerivedFunctor ηg
          (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂
            CommRingCat
            RingCat)).obj B)) (ComplexShape.up ℤ)) ∧
      Rgf.IsRightDerivedFunctor ηgf
          (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
            CommRingCat
            RingCat)).obj A)) (ComplexShape.up ℤ)) ∧
      (∀ (I : CochainComplex (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat
        RingCat)).obj A)) ℤ),
        I.IsKInjective → IsIso (ηf.app I) ∧ IsIso (ηgf.app I)) ∧
      (∀ (T : CochainComplex (ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat
        RingCat)).obj B)) ℤ),
        T.IsKInjective → IsIso (ηg.app T)) ∧
      ∃! κ : Rgf ≅ Rf ⋙ Rg,
        (∀ (M : CochainComplex (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat
          RingCat)).obj A)) ℤ),
          ηgf.app M ≫ κ.hom.app (DerivedCategory.Q.{w}.obj M) =
            ηg.app ((f.modules.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
              Rg.map (ηf.app M)) ∧
        ∀ (I : CochainComplex (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat
          RingCat)).obj A)) ℤ),
          I.IsKInjective → ∀ (T : CochainComplex (ringedSiteModules.{u, u, u, u} ((sheafCompose K
            (forget₂
            CommRingCat RingCat)).obj B)) ℤ),
          T.IsKInjective →
          ∀ (j : (f.modules.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ T),
          ∀ [QuasiIso j],
          QuasiIso ((g.modules.mapHomologicalComplex (ComplexShape.up ℤ)).map j) ∧
          ηgf.app I ≫ κ.hom.app (DerivedCategory.Q.{w}.obj I) =
            DerivedCategory.Q.{w}.map
                ((g.modules.mapHomologicalComplex (ComplexShape.up ℤ)).map j) ≫
              ηg.app T ≫ Rg.map (inv (DerivedCategory.Q.{w}.map j) ≫ ηf.app I)
```

## New

```lean
theorem ringedToposDerivedPushforwardComposition
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E)
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (R : Sheaf L CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj
      A))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat.{u}
      RingCat.{u})).obj
      B))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose L (forget₂ CommRingCat.{u}
      RingCat.{u})).obj
      R))]
    (f : RingedToposMorphism.{u} (C := C) (D := D) (J := J) (K := K)
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A)
      ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj B))
    (g : RingedToposMorphism.{u} (C := D) (D := E) (J := K) (K := L)
      ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj B)
      ((sheafCompose L (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    ∃ (Rf : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
      CommRingCat.{u}
      RingCat.{u})).obj
      A)) ⥤
          DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
            ((sheafCompose K (forget₂ CommRingCat.{u}
            RingCat.{u})).obj
            B)))
      (Rg : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂
        CommRingCat.{u}
        RingCat.{u})).obj
        B)) ⥤
          DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
            ((sheafCompose L (forget₂ CommRingCat.{u}
            RingCat.{u})).obj
            R)))
      (Rgf : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
        CommRingCat.{u}
        RingCat.{u})).obj A)) ⥤
          DerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
            ((sheafCompose L (forget₂ CommRingCat.{u}
            RingCat.{u})).obj
            R)))
      (ηf : f.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ Rf)
      (ηg : g.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ Rg)
      (ηgf : (f.modules ⋙ g.modules).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ Rgf),
      Rf.IsRightDerivedFunctor ηf
          (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
            CommRingCat.{u}
            RingCat.{u})).obj A)) (ComplexShape.up ℤ)) ∧
      Rg.IsRightDerivedFunctor ηg
          (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂
            CommRingCat.{u}
            RingCat.{u})).obj B)) (ComplexShape.up ℤ)) ∧
      Rgf.IsRightDerivedFunctor ηgf
          (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
            CommRingCat.{u}
            RingCat.{u})).obj A)) (ComplexShape.up ℤ)) ∧
      (∀ (I : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat.{u}
        RingCat.{u})).obj A)) ℤ),
        I.IsKInjective → IsIso (ηf.app I) ∧ IsIso (ηgf.app I)) ∧
      (∀ (T : CochainComplex (ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat.{u}
        RingCat.{u})).obj B)) ℤ),
        T.IsKInjective → IsIso (ηg.app T)) ∧
      ∃! κ : Rgf ≅ Rf ⋙ Rg,
        (∀ (M : CochainComplex (ringedSiteModules.{u, u, u, u}
          ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj A)) ℤ),
          ηgf.app M ≫ κ.hom.app (DerivedCategory.Q.{w}.obj M) =
            ηg.app ((f.modules.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
              Rg.map (ηf.app M)) ∧
        ∀ (I : CochainComplex (ringedSiteModules.{u, u, u, u}
          ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj A)) ℤ),
          I.IsKInjective → ∀ (T : CochainComplex (ringedSiteModules.{u, u, u, u} ((sheafCompose K
            (forget₂
            CommRingCat.{u} RingCat.{u})).obj B)) ℤ),
          T.IsKInjective →
          ∀ (j : (f.modules.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ T),
          ∀ [QuasiIso j],
          QuasiIso ((g.modules.mapHomologicalComplex (ComplexShape.up ℤ)).map j) ∧
          ηgf.app I ≫ κ.hom.app (DerivedCategory.Q.{w}.obj I) =
            DerivedCategory.Q.{w}.map
                ((g.modules.mapHomologicalComplex (ComplexShape.up ℤ)).map j) ≫
              ηg.app T ≫ Rg.map (inv (DerivedCategory.Q.{w}.map j) ≫ ηf.app I)
```

## Users

The import graph has 486 downstream modules. A whole-word search finds no
use of `ringedToposDerivedPushforwardComposition` outside its declaring module;
the current parents import its statement as part of their planned dependencies.
The explicit annotations are definitionally the inferred arguments, so every
existing application would remain valid. No downstream file needs adaptation,
and no target definition or statement changes. The table records the full import
downstream set and current claims at preparation time.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineCurveCohomologicalDimension | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSupportVanishing | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactBoundedConstructibleBaseChange | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstantFiniteComparison | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleFiniteSurjectionCancellation | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImagesComp | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModificationTransfer | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportBaseChangeQcqs | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleOpenProperInterchange | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteBoundaryComparison | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteBoundaryReconstruction | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricFiberFinite | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralSurjectiveTargetBaseChange | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.LerayBounded | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ModificationExtensionZero | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteObjectwise | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveCurveConstant | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroup | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineConstructible | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSmoothCurveFiniteness | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBoundedConstructible | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperCaseConstructibility | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperConstructibleHigherDirectImages | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonComposition | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonIso | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperProjectionFormula | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeDimensionOneInduction | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.CohomologicalDimensionGroundField | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionSheafProperBaseChange | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison | F4 | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.UnboundedCoefficientForgetfulAux | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.UniversalBaseChangeFailureDatum | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.AlgebraicGeometry.UniversalCurveTestVanishing | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Same kernel signature; no adaptation. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures | unclaimed | Same kernel signature; no adaptation. |
| TargetsCheck | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceAdjunction | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceTrace | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicallySmooth | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.FamilyObject | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.FrameIndependence | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductAppend | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.ShiftTateObjectAssoc | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClass | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Trace | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.TateTwist.Basic | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.TateTwist.KummerClass | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.EtaleCohomology.TateTwist.Normalized | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.ArtinSchreierVanishing | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Convolution | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Unit | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.UnitVanishing | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.FourierTransform.ArtinSchreierCohomology | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.FourierTransform.Composition | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Dualizing | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupportBaseChange | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteBoundary | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteComparison | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Kunneth | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Modification | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Projective | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.TargetLocal | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ClosedImmersion | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryCompactSupport | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryProper | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Localization | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocallyConstantInvertible | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekReduction | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.TateTwist | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Point | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Shift | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ShiftAssoc | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SingleDelta | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.TorSheaf | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsBaseChange | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsEtale | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsOpenImmersion | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Triangulated | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriek | XRdbb7091a3d1839f4 | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsComposition | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekOpenRestriction | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Pairing | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Basic | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.DualPerfect | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Duality | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Finiteness | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.HomComparison | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationConstructible | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationFiniteTor | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekBaseChange | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekIndependence | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormula | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormulaExtendScalars | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ScalarExtension | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Stability | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Additivity | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Adic | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobenius | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusLift | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusTrace | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicRange | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicSystem | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineLine | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineReduction | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Curve | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Defs | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.FiniteModel | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.FixedPoints | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.GlobalOperator | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Iterate | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.KernelPushforward | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.LocalFrobenius | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Localization | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Main | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ModelRestriction | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Perfectness | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperCurve | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperPushforward | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardFibres | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardStep | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.RelativeAffineLine | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceClass | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceFormulaHolds | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceMap | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.WeaklyContractibleCohomology | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.Statement | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.HomologyShift | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.ZetaFunction.SixOperations | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same kernel signature; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same kernel signature; no adaptation. |

## Status

landed 20261015T221655-L-2639332 2026-10-15 (merge of deliver/H4/Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition)
