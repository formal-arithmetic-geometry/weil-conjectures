# AlgebraicGeometry.Etale.exists_etale_complex_class_rep

## Reason
Remove unused imports after the finite-filtration reduction. The theorem signature
is unchanged. The public Mathlib imports were needed by neither the declaration
nor its new proof. The sole direct importer, EtaleComplexCohomologyLimit, already
publicly imports both Mathlib modules itself, so their exposure to every further
importer is preserved. No target meaning changes and no target review is reopened.
No dependent file requires adaptation. No module owned by another group is edited.

## Old
```lean
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence
import Sheaf.CategoryTheory.HypercohomologyFirstPage
import Sheaf.CategoryTheory.KInjectiveBridge
import Sheaf.CategoryTheory.SpectralSequenceComparison
import Sheaf.CategoryTheory.ExistsDirectedReindexing
import Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial

theorem exists_etale_complex_class_rep
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : I) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ)
    (φ : ∀ {i j : I} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{u + 1} (D.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i)))
        (ComplexShape.up ℤ)).hom.app (F i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} (D.obj i))
        (ComplexShape.up ℤ)).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : j ⟶ i) (g : k ⟶ j),
      φ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (D.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ φ g)
    (a : ℤ) (hbelow : ∀ (i : I) (n : ℤ), n < a → IsZero ((F i).X n))
    (G : Iᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (eG : ∀ i : I, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i))
    (hG : ∀ (i j : I) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ (eG j).inv)
    (p : ℤ)
    (P : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      (cohomology AddCommGrpCat.{u + 1} Y p).obj (DerivedCategory.Q.obj K) ⟶
      (cohomology AddCommGrpCat.{u + 1} X p).obj
        (DerivedCategory.Q.obj
          (((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)))
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      P f K = (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} p).map
        ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
          ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
            (DerivedCategory.Q.obj K)) ≫
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar AddCommGrpCat.{u + 1} f)
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1})
          (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{u + 1} f)
              (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
                terminalIsTerminal) ≪≫
            lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f ≪≫
            (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
              terminalIsTerminal).symm)).hom.app
                ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj
                  (DerivedCategory.Q.obj K)) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
          ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryFactors.hom.app K)))
    (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj (op i) ≅
      (cohomology AddCommGrpCat.{u + 1} (D.obj i) p).obj (DerivedCategory.Q.obj (F i)))
    (hH : ∀ (i j : I) (f : j ⟶ i), H.map f.op =
      (eH i).hom ≫ P (D.map f) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} (D.obj j) p).map
          (DerivedCategory.Q.map (φ f)) ≫ (eH j).inv)
    (L : Cocone G) (hL : IsColimit L)
    (B : Cocone H)
    (eB : B.pt ≅ (cohomology AddCommGrpCat.{u + 1} c.pt p).obj
      (DerivedCategory.Q.obj L.pt))
    (hB : ∀ i : I, B.ι.app (op i) ≫ eB.hom =
      (eH i).hom ≫ P (c.π.app i) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} c.pt p).map
          (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i)))) :
    ∀ x : B.pt, ∃ (i : I) (y : H.obj (op i)), B.ι.app (op i) y = x
```

## New
```lean
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import Sheaf.AlgebraicGeometry.EtaleComplexGradedClassDescent

theorem exists_etale_complex_class_rep
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : I) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ)
    (φ : ∀ {i j : I} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{u + 1} (D.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i)))
        (ComplexShape.up ℤ)).hom.app (F i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} (D.obj i))
        (ComplexShape.up ℤ)).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : j ⟶ i) (g : k ⟶ j),
      φ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (D.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ φ g)
    (a : ℤ) (hbelow : ∀ (i : I) (n : ℤ), n < a → IsZero ((F i).X n))
    (G : Iᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (eG : ∀ i : I, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i))
    (hG : ∀ (i j : I) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ (eG j).inv)
    (p : ℤ)
    (P : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      (cohomology AddCommGrpCat.{u + 1} Y p).obj (DerivedCategory.Q.obj K) ⟶
      (cohomology AddCommGrpCat.{u + 1} X p).obj
        (DerivedCategory.Q.obj
          (((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)))
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      P f K = (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} p).map
        ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
          ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
            (DerivedCategory.Q.obj K)) ≫
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar AddCommGrpCat.{u + 1} f)
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1})
          (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{u + 1} f)
              (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
                terminalIsTerminal) ≪≫
            lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f ≪≫
            (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
              terminalIsTerminal).symm)).hom.app
                ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj
                  (DerivedCategory.Q.obj K)) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
          ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryFactors.hom.app K)))
    (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj (op i) ≅
      (cohomology AddCommGrpCat.{u + 1} (D.obj i) p).obj (DerivedCategory.Q.obj (F i)))
    (hH : ∀ (i j : I) (f : j ⟶ i), H.map f.op =
      (eH i).hom ≫ P (D.map f) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} (D.obj j) p).map
          (DerivedCategory.Q.map (φ f)) ≫ (eH j).inv)
    (L : Cocone G) (hL : IsColimit L)
    (B : Cocone H)
    (eB : B.pt ≅ (cohomology AddCommGrpCat.{u + 1} c.pt p).obj
      (DerivedCategory.Q.obj L.pt))
    (hB : ∀ i : I, B.ι.app (op i) ≫ eB.hom =
      (eH i).hom ≫ P (c.π.app i) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} c.pt p).map
          (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i)))) :
    ∀ x : B.pt, ∃ (i : I) (y : H.obj (op i)), B.ι.app (op i) y = x
```
The existing signature above is byte for byte identical in Old and New. The new
proof-only graded lifting module has no existing downstream users and changes
no existing statement or definition.

## Users
Read-only `tools/downstream.py Sheaf.AlgebraicGeometry.EtaleComplexClassDescent
--uses exists_etale_complex_class_rep` lists 153 transitive importers and only one
external textual user of the theorem, EtaleComplexCohomologyLimit. Its unchanged
public imports supply both removed Mathlib modules to the entire downstream
closure. Thus all the following signatures and definitions keep their meanings.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | B3 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.ConstantModulePushforwardLimit | N1 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | B3 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData | N2 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | C2 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | U2 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | D2 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | U1 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | N1 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | P1 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | N1 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | A2 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | Q1 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit | none recorded | Sole direct importer. It already publicly imports both removed Mathlib modules; unchanged theorem application needs no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.GmStrictHenselizationStalkFormula | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem | U2 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.IntegralConstantModulePushforwardColimit | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison | H1 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk | M1 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| TargetsCheck | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | T2 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | X2 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.FourierTransform.AffineSpace | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.FourierTransform.Defs | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.FourierTransform.Inversion | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.FourierTransform.Perverse | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.FourierTransform.Properties | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.FourierTransform.Properties.BaseChange | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.FourierTransform.Properties.Stalk | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Gabber | Q2 | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | none recorded | The theorem type is identical; no definition changes. Public Mathlib exposure is retained by the direct importer. |

## Status
landed 20261012T070532-L-3468502 2026-10-12 (merge of deliver/D2/Sheaf.AlgebraicGeometry.EtaleComplexClassDescent)
