# finite_exactHom_single_counit_transport private proof context

## Reason

The delivery adds three proved private generic helpers. Its extra universe, open,
namespace, section-variable and option commands make the conservative interface check
request a change record. All generic context is enclosed in `section ProofAssembly`.
The original public theorem signature and public imports remain byte-for-byte identical.
The only compiler option change is local to that theorem, restoring compilation below
60 seconds without changing any definition or elaborated mathematical statement.

No target statement or definition changes meaning, so no target review is reopened.
The private helpers cannot be referenced from downstream public signatures.

## Old

The original declaration context, verbatim:

```lean
universe u wX wY wA

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option maxHeartbeats 800000 in
-- Elaborating the canonical factorization unfolds the two ring-sheaf presentations.
```

## New

The new local generic context and restored original public context, verbatim:

```lean
section ProofAssembly

universe uC uA uB vC vA vB wC wDA wB
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace CategoryTheory
variable {C : Type uC} {A : Type uA} {B : Type uB}
  [Category.{vC} C] [Category.{vA} A] [Category.{vB} B]
  [Abelian C] [Abelian A] [Abelian B]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wDA} A]
  [HasDerivedCategory.{wB} B] [HasKInjectiveResolutions C]
  [HasKInjectiveResolutions A] [HasKInjectiveResolutions B]
omit [HasKInjectiveResolutions B] in
private theorem derivedNatIso_refl (F : C ⥤ B) [F.Additive] :
    Functor.rightDerivedFunctorNatIso (Iso.refl F) = Iso.refl F.rightDerivedFunctor := by
  ext
  simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]

private theorem assembly (F : C ⥤ A) (T : A ⥤ B) (H : B ⥤ A)
    [F.Additive] [T.Additive] [H.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [T.ReflectsIsomorphisms]
    (adj : T ⊣ H) (M : C) (L : B)
    (hcf : IsIso (DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (F ⋙ T)
        (ComplexShape.up ℤ) 0).inv.app M) ≫
      (F ⋙ T).rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
        ((CochainComplex.singleFunctor C 0).obj M))))
    (e : F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M) ≅
      H.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor B 0).obj L)) :
    ∃ j : F.obj M ≅ H.obj L,
      (DerivedCategory.singleFunctor B 0).map (T.map j.hom ≫ adj.counit.app L) =
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex (F ⋙ T)
          (ComplexShape.up ℤ) 0).inv.app M) ≫
        (F ⋙ T).rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
          ((CochainComplex.singleFunctor C 0).obj M)) ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F T).hom.app
          ((DerivedCategory.singleFunctor C 0).obj M) ≫
        T.mapDerivedCategory.map e.hom ≫
        adj.mapDerivedCategoryRightDerivedAdjunction.counit.app
          ((DerivedCategory.singleFunctor B 0).obj L) := by
  classical
  let K := (CochainComplex.singleFunctor C 0).obj M
  let cg : (DerivedCategory.singleFunctor A 0).obj (F.obj M) ⟶
      F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M) :=
    DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M) ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K)
  let cf : (DerivedCategory.singleFunctor B 0).obj (T.obj (F.obj M)) ⟶
      (F ⋙ T).rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M) :=
    DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex (F ⋙ T)
      (ComplexShape.up ℤ) 0).inv.app M) ≫
    (F ⋙ T).rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K)
  let t := (T.mapDerivedCategorySingleFunctor 0).app (F.obj M)
  let g := (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F T).app
    ((DerivedCategory.singleFunctor C 0).obj M)
  have hcomp : t.inv ≫ T.mapDerivedCategory.map cg ≫ g.inv = cf :=
    F.single_rightDerived_exact_composition T M
  have : T.mapDerivedCategory.ReflectsIsomorphisms := by
    constructor
    intro P Q a ha
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso ((DerivedCategory.homologyFunctor _ n ⋙ T).map a) :=
      (NatIso.isIso_map_iff (T.mapDerivedCategoryHomologyFunctorIso n) a).mpr
        (by dsimp; infer_instance)
    have : IsIso (T.map ((DerivedCategory.homologyFunctor A n).map a)) := ‹_›
    exact isIso_of_reflects_iso ((DerivedCategory.homologyFunctor _ n).map a) T
  have : IsIso (t.inv ≫ T.mapDerivedCategory.map cg ≫ g.inv) := by
    rw [hcomp]
    exact hcf
  have : IsIso (T.mapDerivedCategory.map cg ≫ g.inv) :=
    IsIso.of_isIso_comp_left t.inv _
  have : IsIso (T.mapDerivedCategory.map cg) := IsIso.of_isIso_comp_right _ g.inv
  have : IsIso cg := isIso_of_reflects_iso cg T.mapDerivedCategory
  let h := H.singleFunctorCompRightDerivedFunctorIso.app L
  let d := asIso cg ≪≫ e ≪≫ h
  let S := DerivedCategory.singleFunctor A 0
  let j := S.preimageIso d
  refine ⟨j, ?_⟩
  have hj : S.map j.hom = cg ≫ e.hom ≫ h.hom := by
    change S.map (S.preimage d.hom) = _
    rw [Functor.map_preimage]
    rfl
  have hcounit := adj.exact_derivedAdjunction_single_counit L
  have heq : (DerivedCategory.singleFunctor B 0).map (T.map j.hom) =
      t.inv ≫ T.mapDerivedCategory.map (S.map j.hom) ≫
        (T.mapDerivedCategorySingleFunctor 0).hom.app (H.obj L) := by
    have hn := (T.mapDerivedCategorySingleFunctor 0).hom.naturality j.hom
    dsimp only [Functor.comp_map] at hn
    exact (t.inv_comp_eq.mpr hn).symm
  have hc : (T.mapDerivedCategorySingleFunctor 0).hom.app (H.obj L) ≫
      (DerivedCategory.singleFunctor B 0).map (adj.counit.app L) =
      T.mapDerivedCategory.map h.inv ≫
        adj.mapDerivedCategoryRightDerivedAdjunction.counit.app
          ((DerivedCategory.singleFunctor B 0).obj L) := hcounit.symm
  simp only [← Category.assoc]
  change (DerivedCategory.singleFunctor B 0).map (T.map j.hom ≫ adj.counit.app L) =
    ((cf ≫ g.hom) ≫ T.mapDerivedCategory.map e.hom) ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app _
  simp only [Category.assoc]
  rw [Functor.map_comp, heq]
  simp only [Category.assoc]
  rw [hc, hj]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc,
    Iso.hom_inv_id, Functor.map_id, Category.id_comp]
  rw [← hcomp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [Functor.map_comp, Category.assoc]
private theorem assembly_transport (F : C ⥤ A) (T : A ⥤ B) (H : B ⥤ A)
    (G : C ⥤ B)
    [F.Additive] [T.Additive] [H.Additive] [G.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [T.ReflectsIsomorphisms]
    (adj : T ⊣ H) (M : C) (L : B) (hFT : F ⋙ T = G)
    (hcf : IsIso (DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex G
        (ComplexShape.up ℤ) 0).inv.app M) ≫
      G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
        ((CochainComplex.singleFunctor C 0).obj M))))
    (γ : F.rightDerivedFunctor ⋙ T.mapDerivedCategory ≅ G.rightDerivedFunctor)
    (hγ : γ = (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F T).symm ≪≫
      Functor.rightDerivedFunctorNatIso (eqToIso hFT))
    (e : F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M) ≅
      H.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor B 0).obj L)) :
    ∃ j : F.obj M ≅ H.obj L,
      (DerivedCategory.singleFunctor B 0).map (T.map j.hom ≫ adj.counit.app L) =
      eqToHom (congrArg (fun J : C ⥤ B =>
        (DerivedCategory.singleFunctor B 0).obj (J.obj M)) hFT) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex G
          (ComplexShape.up ℤ) 0).inv.app M) ≫
        G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
          ((CochainComplex.singleFunctor C 0).obj M)) ≫
        γ.inv.app ((DerivedCategory.singleFunctor C 0).obj M) ≫
        T.mapDerivedCategory.map e.hom ≫
        adj.mapDerivedCategoryRightDerivedAdjunction.counit.app
          ((DerivedCategory.singleFunctor B 0).obj L) := by
  subst G
  simp only [eqToIso_refl, derivedNatIso_refl, Iso.trans_refl] at hγ
  subst γ
  simpa only [eqToHom_refl, Category.id_comp, Iso.symm_inv] using
    assembly F T H adj M L hcf e

end CategoryTheory

end ProofAssembly

universe u wX wY wA

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.lazyWhnfCore false in
set_option maxHeartbeats 800000 in
-- Elaborating the canonical factorization unfolds the two ring-sheaf presentations.
```

Every existing declaration retains its signature and visibility. The generic context
ends before the public theorem; the additional option also ends with that theorem.
No existing module besides the held item is modified.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteExactHomSingleCounitTransport
--uses AlgebraicGeometry.finite_exactHom_single_counit_transport` finds one external
textual user, `FiniteExactHomDegreeZeroLift`, and the item itself. That external user's
application still has exactly the same declaration type. The transitive module scan
lists the following modules; none sees a changed definition or signature. Holders are
from the local claim snapshot at preparation time.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FiniteExactHomSingleCounitTransport | K2 | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | D3 | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | H2 | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.FibreCartierLocal | S3 | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteDualityDegreeZeroCounitAction | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteExactHomDegreeZeroLift | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteFlatDualityEvaluation | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier | Q1 | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | Y2 | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier | W3 | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| TargetsCheck | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Unchanged public declarations and meanings; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Unchanged public declarations and meanings; no adaptation. |

## Status

landed 20261012T235555-L-2201444 2026-10-12 (merge of deliver/K2/Sheaf.AlgebraicGeometry.FiniteExactHomSingleCounitTransport)
