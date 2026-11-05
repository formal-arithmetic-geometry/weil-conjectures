/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.SmoothPurity.RhomGlobalSectionsOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import Mathlib.Algebra.Category.Grp.EpiMono
import all WeilConjectures.CategoryTheory.SmoothPurity.HomComplexGlobalHomotopyOfUniverses
import WeilConjectures.AlgebraicGeometry.Sites.KInjectiveComparisonPrinciple
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor

/-! # Canonical zero-cycle class in derived global Hom

Source: Stacks Project, Tags 08JA and 079P
(blueprint: def-coef-hom-zero-cycle-class).

## Main definitions

- `coefficientGlobalSections`: the recorded total derived section functor.
- `coefficientHomZeroClass`: the actual zero-cycle class via the derived unit.
- `coefficientHomZeroEvaluation`: evaluation by the fixed product projections.
- `coefficientHomZeroEquiv`: the uniquely normalized recorded H⁰ RHom identification.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
universe u c v a b w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] homComplexFunctor

section RightDerivedUnit

variable {D E : Type*} [Category* D] [Category* E] [Abelian D] [Abelian E]
  [HasDerivedCategory D] [HasDerivedCategory E] [Abelian.HasKInjectiveResolutions D]

@[no_expose] private noncomputable def zeroRightDerivedUnitNatTrans
    (F : D ⥤ E) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app K := F.rightDerivedFunctorUnitQ K
  naturality {_X _Y} f := F.rightDerivedFunctorUnitQ_naturality f

end RightDerivedUnit

section DerivedHomotopyComparison

variable {D : Type a} [Category.{v} D] [Abelian D] [HasDerivedCategory.{w} D]
  (I : CochainComplex D ℤ ⥤ CochainComplex D ℤ)
  (η : 𝟭 (CochainComplex D ℤ) ⟶ I)
  (hI : ∀ M, (I.obj M).IsKInjective) (hη : ∀ M, QuasiIso (η.app M))

@[no_expose] private noncomputable def zeroResolutionInverse (M : CochainComplex D ℤ) :
    DerivedCategory.Q.obj (I.obj M) ⟶ DerivedCategory.Q.obj M :=
  letI := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr (hη M)
  inv (DerivedCategory.Q.map (η.app M))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 300000 in
-- The homotopy-localization comparison checks its chosen localization functors.
@[no_expose] private noncomputable def zeroDerivedHomotopyIso :
    (HomotopyCategory.quotient D (.up ℤ)).op.prod
        (I ⋙ HomotopyCategory.quotient D (.up ℤ)) ⋙
      Functor.uncurry.obj (preadditiveCoyoneda (C := HomotopyCategory D (.up ℤ))) ⋙
        AddCommGrpCat.uliftFunctor.{w, v} ≅
      DerivedCategory.Q.op.prod DerivedCategory.Q ⋙
        Functor.uncurry.obj (preadditiveCoyoneda (C := DerivedCategory D)) ⋙
          AddCommGrpCat.uliftFunctor.{v, w} := by
  classical
  let q := HomotopyCategory.quotient D (ComplexShape.up ℤ)
  let Q := DerivedCategory.Q (C := D)
  let σ := DerivedCategory.quotientCompQhIso D
  let H := Functor.uncurry.obj (preadditiveCoyoneda (C := DerivedCategory D))
  let HK := Functor.uncurry.obj
    (preadditiveCoyoneda (C := HomotopyCategory D (ComplexShape.up ℤ)))
  let U := AddCommGrpCat.uliftFunctor.{w, v}
  let V := AddCommGrpCat.uliftFunctor.{v, w}
  let B := q.op.prod (I ⋙ q) ⋙ HK ⋙ U
  let T := Q.op.prod Q ⋙ H ⋙ V
  have hi (M : CochainComplex D ℤ) : IsIso (Q.map (η.app M)) := by
    have := hη M
    infer_instance
  let t (P : (CochainComplex D ℤ)ᵒᵖ × CochainComplex D ℤ) :
      (DerivedCategory.Qh.obj (q.obj P.1.unop) ⟶
        DerivedCategory.Qh.obj (q.obj (I.obj P.2))) ≃+
      (Q.obj P.1.unop ⟶ Q.obj P.2) := by
    have := hi P.2
    exact
      { toEquiv := Iso.homCongr (σ.app P.1.unop)
          (σ.app (I.obj P.2) ≪≫ (asIso (Q.map (η.app P.2))).symm)
        map_add' := by intros; simp [Preadditive.comp_add, Preadditive.add_comp] }
  let e (P : (CochainComplex D ℤ)ᵒᵖ × CochainComplex D ℤ) : B.obj P ≃+ T.obj P :=
    AddEquiv.ulift.trans
      ((AddEquiv.ofBijective (DerivedCategory.Qh.mapAddHom)
        (by have := hI P.2; exact CochainComplex.IsKInjective.Qh_map_bijective _ _)).trans
        ((t P).trans AddEquiv.ulift.symm))
  let b : B ≅ T := NatIso.ofComponents (fun P ↦ (e P).toAddCommGrpIso) (by
    intro P P' f
    ext x
    apply ULift.ext
    dsimp [B, T, e, t, HK, H, U, V, Functor.uncurry,
      preadditiveCoyoneda, preadditiveCoyonedaObj, AddCommGrpCat.uliftFunctor,
      AddEquiv.toAddCommGrpIso, AddEquiv.ofBijective, Iso.homCongr,
      AddEquiv.ulift, Equiv.ulift, Functor.mapAddHom]
    have := hi P.2
    have := hi P'.2
    have hn : Q.map (I.map f.2) ≫ inv (Q.map (η.app P'.2)) =
        inv (Q.map (η.app P.2)) ≫ Q.map f.2 := by
      apply (cancel_epi (Q.map (η.app P.2))).mp
      rw [← Category.assoc, ← Q.map_comp, ← η.naturality f.2, Q.map_comp]
      simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id,
        IsIso.hom_inv_id_assoc, Functor.id_map]
    simp only [AddMonoidHom.mk'_apply, Functor.map_comp, Category.assoc]
    dsimp only [σ]
    rw [← DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
    rw [DerivedCategory.quotientCompQhIso_hom_naturality_assoc]
    rw [hn])
  exact b

attribute [local irreducible] zeroDerivedHomotopyIso

end DerivedHomotopyComparison

section AssociativeLocalizationComparison

variable {S T K₀ D E G H : Type*}
  [Category* S] [Category* T] [Category* K₀] [Category* D]
  [Category* E] [Category* G] [Category* H]
  (P : S ⥤ T) (R : T ⥤ D) (B : S ⥤ K₀) (Q : K₀ ⥤ D)
  (Γ : D ⥤ E) (H₀ : E ⥤ G) (U : G ⥤ H) (e : P ⋙ R ≅ B ⋙ Q)

@[no_expose] private noncomputable def zeroAssociativeLocalizationIso :
    P ⋙ R ⋙ (Γ ⋙ H₀) ⋙ U ≅ (B ⋙ Q ⋙ Γ ⋙ H₀) ⋙ U :=
  (Functor.associator P R ((Γ ⋙ H₀) ⋙ U)).symm ≪≫
    Functor.isoWhiskerRight e ((Γ ⋙ H₀) ⋙ U) ≪≫
      (Functor.associator (B ⋙ Q) (Γ ⋙ H₀) U).symm ≪≫
        Functor.isoWhiskerRight (Functor.associator B Q (Γ ⋙ H₀)) U

attribute [local irreducible] zeroAssociativeLocalizationIso

end AssociativeLocalizationComparison

section UnliftHomComparison

variable {D : Type a} [Category.{w} D] [Preadditive D]
  (F : Dᵒᵖ × D ⥤ AddCommGrpCat.{v})
  (z : F ⋙ AddCommGrpCat.uliftFunctor.{w, v} ≅
    Functor.uncurry.obj (preadditiveCoyoneda (C := D)) ⋙
      AddCommGrpCat.uliftFunctor.{v, w})

@[no_expose] private noncomputable def zeroUnliftHomEquiv (P : Dᵒᵖ × D) :
    F.obj P ≃+ (P.1.unop ⟶ P.2) :=
  AddEquiv.ulift.symm.trans
    ((z.app P).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)

attribute [local irreducible] zeroUnliftHomEquiv

end UnliftHomComparison

set_option backward.isDefEq.respectTransparency false in
@[no_expose] private noncomputable def zeroGlobalHomologyNatIsoOfComplexIso
    {D : Type a} [Category.{v} D] [Preadditive D]
    (F : (CochainComplex D ℤ)ᵒᵖ × CochainComplex D ℤ ⥤
      CochainComplex AddCommGrpCat.{v} ℤ)
    (e : ∀ X, F.obj X ≅ CochainComplex.HomComplex X.1.unop X.2)
    (he : ∀ {X Y} (f : X ⟶ Y), F.map f ≫ (e Y).hom =
      (e X).hom ≫ CategoryTheory.externalMap f.1.unop f.2) :
    F ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) 0 ≅
      (HomotopyCategory.quotient
        D
          (.up ℤ)).op.prod (HomotopyCategory.quotient _ (.up ℤ)) ⋙
        Functor.uncurry.obj preadditiveCoyoneda := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) 0
  let q := HomotopyCategory.quotient
    D (.up ℤ)
  let iso : F ⋙ H ≅
      q.op.prod q ⋙ Functor.uncurry.obj preadditiveCoyoneda :=
    NatIso.ofComponents
      (fun X ↦ H.mapIso (e X) ≪≫
        CategoryTheory.externalHomologyIso X.1.unop X.2) (by
      intro X Y f
      have h : H.map ((F).map f) ≫
          H.map (e Y).hom =
          H.map (e X).hom ≫
            H.map (CategoryTheory.externalMap f.1.unop f.2) := by
        simpa only [Functor.map_comp, Quiver.Hom.op_unop, Prod.mk.eta] using
          H.congr_map (he f)
      dsimp only [H, q] at h ⊢
      simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
      rw [← Category.assoc, h, Category.assoc]
      change H.map (e X).hom ≫
          HomologicalComplex.homologyMap (CategoryTheory.externalMap f.1.unop f.2) 0 ≫
            (CategoryTheory.externalHomologyIso Y.1.unop Y.2).hom = _
      rw [CategoryTheory.externalHomologyIso_naturality]
      ext a
      change (q.map f.1.unop ≫ _ ≫ q.map f.2) = _
      exact (Category.assoc _ _ _).symm)
  exact iso

@[irreducible, no_expose] private noncomputable def zeroWhiskerLeft
    {B D E : Type*} [Category* B] [Category* D] [Category* E]
    (S : B ⥤ D) {F G : D ⥤ E} (α : F ⟶ G) : S ⋙ F ⟶ S ⋙ G :=
  Functor.whiskerLeft S α

@[irreducible, no_expose] private noncomputable def zeroWhiskerLeftAssoc
    {B D E Z : Type*} [Category* B] [Category* D] [Category* E] [Category* Z]
    (S : B ⥤ D) {F : D ⥤ E} {G : E ⥤ Z} {T : D ⥤ Z}
    (α : F ⋙ G ⟶ T) : (S ⋙ F) ⋙ G ⟶ S ⋙ T :=
  zeroWhiskerLeft S α

@[irreducible, no_expose] private noncomputable def zeroWhiskerLeftAssocIso
    {B D E Z V : Type*} [Category* B] [Category* D] [Category* E] [Category* Z] [Category* V]
    (S : B ⥤ D) (F : D ⥤ E) (G : E ⥤ Z) (H : Z ⥤ V) {T : D ⥤ V}
    (e : (F ⋙ G) ⋙ H ≅ T) : ((S ⋙ F) ⋙ G) ⋙ H ≅ S ⋙ T :=
  Functor.isoWhiskerLeft S e

section HomZeroRepresentatives

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

attribute [local irreducible] CategoryTheory.globalComplexIso

@[no_expose] private noncomputable def zeroGlobalComplexIso
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ) :
    coefficientHomSectionComplex.{u, c, v} J A L M ≅
      CochainComplex.HomComplex L ((coefficientHomResolution.{u, c, v} J A).obj M) :=
  CategoryTheory.globalComplexIso.{c, v, u} A
    (op L, (coefficientHomResolution.{u, c, v} J A).obj M)

@[no_expose] private noncomputable def zeroCycleCocycle
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ) :
    (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0 ≅
      AddCommGrpCat.of (CochainComplex.HomComplex.Cocycle L
        ((coefficientHomResolution.{u, c, v} J A).obj M) 0) :=
  HomologicalComplex.cyclesMapIso (zeroGlobalComplexIso.{u, c, v} J A L M) 0 ≪≫
    (CochainComplex.HomComplex.leftHomologyData L
      ((coefficientHomResolution.{u, c, v} J A).obj M) 0).cyclesIso

attribute [local irreducible] zeroCycleCocycle

set_option backward.isDefEq.respectTransparency false in
@[no_expose] private noncomputable def zeroGlobalHomologyNatIso :
    CategoryTheory.globalBifunctor.{c, v, u} A ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v u} (.up ℤ) 0 ≅
      (HomotopyCategory.quotient
        (SheafOfModules.{max c v u}
          ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))
          (.up ℤ)).op.prod (HomotopyCategory.quotient _ (.up ℤ)) ⋙
        Functor.uncurry.obj preadditiveCoyoneda :=
  zeroGlobalHomologyNatIsoOfComplexIso
    (CategoryTheory.globalBifunctor.{c, v, u} A)
    (CategoryTheory.globalComplexIso.{c, v, u} A)
    (fun {_X _Y} f ↦ zeroGlobalComplexIso_naturality.{u, c, v} J A f)

attribute [local irreducible] zeroGlobalHomologyNatIso

set_option hygiene false in
local notation "Mod" => SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)
set_option hygiene false in
local notation "K" => CochainComplex Mod ℤ
set_option hygiene false in
local notation "Der" => DerivedCategory Mod

@[no_expose] private noncomputable def zeroHomLocalizationNatIso :
    DerivedCategory.Q.op.prod DerivedCategory.Q ⋙
        derivedInternalHomOfUniverses.{c, v, u, w} J A ≅
      (𝟭 Kᵒᵖ).prod (coefficientHomResolution.{u, c, v} J A) ⋙
        Functor.uncurry.obj (homComplexFunctor (R := A)) ⋙ DerivedCategory.Q := by
  let : IsGrothendieckAbelian.{max c v u} Mod := zeroGrothendieck.{u, c, v} J A
  exact Localization.fac
    ((𝟭 _).prod (CochainComplex.kInjectiveResolutionFunctor.{max c v u} _) ⋙
      Functor.uncurry.obj (homComplexFunctor.{c, v, max c v u, max c v u} (R := A)) ⋙
        DerivedCategory.Q)
    (derivedInternalHomOfUniverses_inverts.{c, v, u, w} J A _
      (CochainComplex.toKInjectiveResolution.{max c v u} _)
      (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v u} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{max c v u} _ M⟩))
    (DerivedCategory.Q.op.prod DerivedCategory.Q)

attribute [local irreducible] zeroHomLocalizationNatIso

@[no_expose] private noncomputable def zeroSectionsComparisonNatTrans :
    (coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (.up ℤ) ⋙
        (@DerivedCategory.Q AddCommGrpCat.{max c v u} _ _
          (HasDerivedCategory.standard _)) ⟶
      DerivedCategory.Q ⋙ coefficientGlobalSections.{u, c, v} J A := by
  let : IsGrothendieckAbelian.{max c v u} Mod := zeroGrothendieck.{u, c, v} J A
  let := HasDerivedCategory.standard AddCommGrpCat.{max c v u}
  exact zeroRightDerivedUnitNatTrans (coefficientOrdinarySections.{u, c, v} J A)

@[no_expose] private noncomputable def zeroSectionsHomologyComparisonNatTrans :
    (coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v u} (.up ℤ) 0 ⟶
      DerivedCategory.Q ⋙ coefficientGlobalSections.{u, c, v} J A ⋙
        (@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
          (HasDerivedCategory.standard _) 0) :=
  (Functor.isoWhiskerLeft
    ((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (.up ℤ))
    (@DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max c v u} _ _
      (HasDerivedCategory.standard _) 0)).inv ≫
    Functor.whiskerRight (zeroSectionsComparisonNatTrans.{u, c, v, w} J A)
      (@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
        (HasDerivedCategory.standard _) 0)

attribute [local irreducible] zeroSectionsHomologyComparisonNatTrans
  DerivedCategory.homologyFunctor
  coefficientGlobalSections coefficientSiteSectionsComparison

@[implicit_reducible, no_expose] private noncomputable def zeroOrdinaryBifunctor (I : K ⥤ K) :
    Kᵒᵖ × K ⥤ AddCommGrpCat.{max c v u} :=
  ((((𝟭 Kᵒᵖ).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := A))) ⋙
    (coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (.up ℤ)) ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v u} (.up ℤ) 0)

@[implicit_reducible, no_expose] private noncomputable def zeroHomotopyBifunctor
    (I : K ⥤ K) : Kᵒᵖ × K ⥤ AddCommGrpCat.{max c v u} :=
  (𝟭 Kᵒᵖ).prod I ⋙
    (HomotopyCategory.quotient Mod (.up ℤ)).op.prod
      (HomotopyCategory.quotient Mod (.up ℤ)) ⋙ Functor.uncurry.obj preadditiveCoyoneda

@[no_expose] private noncomputable def zeroOrdinaryBifunctorIso (I : K ⥤ K) :
    zeroOrdinaryBifunctor.{u, c, v} J A I ≅ zeroHomotopyBifunctor.{u, c, v} J A I :=
  zeroWhiskerLeftAssocIso ((𝟭 Kᵒᵖ).prod I)
    (Functor.uncurry.obj (homComplexFunctor (R := A)))
    ((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (.up ℤ))
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{max c v u} (.up ℤ) 0)
    (zeroGlobalHomologyNatIso.{u, c, v} J A)

@[no_expose] private noncomputable def zeroHomSectionsComparisonNatTrans (I : K ⥤ K) :
    zeroOrdinaryBifunctor.{u, c, v} J A I ⟶
      ((𝟭 Kᵒᵖ).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := A))) ⋙
        DerivedCategory.Q ⋙ coefficientGlobalSections.{u, c, v} J A ⋙
          (@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
            (HasDerivedCategory.standard _) 0) :=
  zeroWhiskerLeftAssoc
    ((𝟭 Kᵒᵖ).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := A)))
    (zeroSectionsHomologyComparisonNatTrans.{u, c, v, w} J A)

attribute [local irreducible] zeroOrdinaryBifunctorIso zeroHomSectionsComparisonNatTrans

attribute [local irreducible] coefficientHomZeroEvaluation derivedInternalHomOfUniverses

end HomZeroRepresentatives

end WeilConjectures
