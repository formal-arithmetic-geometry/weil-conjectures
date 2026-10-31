/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import WeilConjectures.Algebra.Homology.SixFunctors.TermwiseConeHomotopyExact
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import all WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Localization.Construction
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Mathlib.CategoryTheory.Functor.Currying
import all Mathlib.CategoryTheory.Whiskering
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Localization.Prod
import all Mathlib.Algebra.Homology.BifunctorFlip
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Localization.CalculusOfFractions
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import all WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-! Precomposition reduction for finite-extension triangulation.
Source: current blueprint, lem-coef-integral-finite-extension.proof.md, paragraphs 1-5
(blueprint: lem-sf-integral-finite-extension-triangulated-precomp).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})

attribute [local instance] ScalarModuleRoosProof.instAdditiveModulePi

private theorem scalar_homotopy_exact :
    ∃ (H : HomotopyCategory (integralTowerModules l E X) (.up ℤ) ⥤
        DerivedCategory (integralTowerModules l L X))
      (_ : integralScalarComplexFunctor l E L ι X ⋙ DerivedCategory.Q ≅
        HomotopyCategory.quotient _ (.up ℤ) ⋙ H)
      (c : H.CommShift ℤ), letI := c; H.IsTriangulated := by
  let F := integralScalarOrdinaryLevel l E L ι X
  let τ := integralScalarModuleTransition l E L ι X
  let P := ScalarModuleRoosProof.modulePi F
  let η := ScalarModuleRoosProof.modulePiEndo F τ
  obtain ⟨H, e, c, h⟩ := CochainComplex.termwiseCone_homotopy_exact P P η
  letI := c
  letI := h
  let π := HomotopyCategory.quotient (integralTowerModules l L X) (.up ℤ)
  let S := CategoryTheory.shiftFunctor
    (HomotopyCategory (integralTowerModules l L X) (.up ℤ)) (-1 : ℤ)
  let Q := DerivedCategory.Qh (C := integralTowerModules l L X)
  let C := CochainComplex.termwiseCone P P η
  let e₀ : integralScalarComplexFunctor l E L ι X ≅
      C ⋙ CategoryTheory.shiftFunctor _ (-1 : ℤ) :=
    eqToIso (integralScalarComplex_eq l E L ι X) ≪≫
      RoosComparisonProof.strictRoosIso F τ ≪≫ Functor.isoWhiskerRight
        (ScalarConeProof.coneFunctorIso (ScalarModuleRoosProof.modulePiComparison F)
          (ScalarModuleRoosProof.modulePiComparison F)
          (ScalarModuleRoosProof.modulePiEndo_comparison F τ)).symm _
  let e₁ : CategoryTheory.shiftFunctor _ (-1 : ℤ) ⋙ DerivedCategory.Q ≅ π ⋙ S ⋙ Q :=
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (π.commShiftIso (-1 : ℤ)) Q ≪≫
      Functor.associator _ _ _
  refine ⟨H ⋙ S ⋙ Q, ?_, inferInstance, inferInstance⟩
  exact Functor.isoWhiskerRight e₀ DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft C e₁ ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e.symm (S ⋙ Q) ≪≫
        Functor.associator _ _ _

-- STATEMENT-DISPUTED (old version): coherence of an arbitrary shift comparison
-- does not imply preservation of distinguished triangles. We construct a shift
-- from chain-level exactness and localization instead.
/-- The derived-quotient precomposition of strict finite-free scalar extension is
triangulated for a shift induced by its chain-level cone construction.
Source: finite-free Roos total-limit triangulation and localization of the
K-flat representative functor. (blueprint: lem-sf-integral-finite-extension-triangulated-precomp)
-/
theorem comparison_precomp_triangulated :
    ∃ (c : (integralScalarExtensionOfUniverses l E L ι X).CommShift ℤ),
      letI := c
      (DerivedCategory.Qh ⋙ integralScalarExtensionOfUniverses l E L ι X).IsTriangulated := by
  classical
  let A := integralTowerModules l E X
  let B := integralTowerModules l L X
  let π := HomotopyCategory.quotient A (.up ℤ)
  let P := integralOperationsGoodComplex l E X
  let T := integralScalarExtensionOfUniverses l E L ι X
  obtain ⟨H, eH, cH, hH⟩ := scalar_homotopy_exact l E L ι X
  letI := cH
  letI := hH
  let good : Set (HomotopyCategory A (.up ℤ)) :=
    {K | ∃ P' : P.FullSubcategory, π.obj P'.obj = K}
  have hres (K : HomotopyCategory A (.up ℤ)) :
      ∃ (K' : HomotopyCategory A (.up ℤ)) (s : K' ⟶ K),
        K' ∈ good ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    obtain ⟨K, rfl⟩ := K.quotient_obj_surjective
    obtain ⟨R, q, hq, hk, hf⟩ := SheafOfModules.functorial_resolution
      (completedIntegralCommRingSheafUnrestricted l E X)
    refine ⟨π.obj (R.obj K), π.map (q.app K), ⟨⟨R.obj K, hk K, hf K⟩, rfl⟩, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 (hq K)
  have hinv (K K' : HomotopyCategory A (.up ℤ)) (s : K ⟶ K')
      (hK : K ∈ good) (hK' : K' ∈ good)
      (hs : HomotopyCategory.quasiIso A (.up ℤ) s) : IsIso (H.map s) := by
    obtain ⟨P₁, rfl⟩ := hK
    obtain ⟨P₂, rfl⟩ := hK'
    let f := π.preimage s
    have hsf : π.map f = s := π.map_preimage s
    have hf : QuasiIso f :=
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 (hsf.symm ▸ hs)
    have hcf := ((integralScalarExtensionWellDefined l E L ι X).1 P₁ P₂ f hf).2
    letI := hcf
    have hi : IsIso ((integralScalarComplexFunctor l E L ι X ⋙ DerivedCategory.Q).map f) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso B _).2 hcf
    have hi' := (NatIso.isIso_map_iff eH f).1 hi
    exact hsf ▸ hi'
  obtain ⟨_, D, ε, _, ⟨cD, hD⟩, hε⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) H good hres hinv
  letI := cD
  letI := hD
  let eQ : P.ι ⋙ DerivedCategory.Q ≅ (P.ι ⋙ π) ⋙ DerivedCategory.Qh :=
    Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso A).symm ≪≫
      (Functor.associator _ _ _).symm
  let εP := Functor.whiskerLeft (P.ι ⋙ π) ε
  have hεP (K : P.FullSubcategory) : IsIso (εP.app K) :=
    hε (π.obj K.obj) ⟨K, rfl⟩
  letI : IsIso εP := NatIso.isIso_of_isIso_app εP
  let eD : integralOperationsGoodLocalization l E X ⋙ D ≅
      integralScalarOnGood l E L ι X :=
    Functor.isoWhiskerRight eQ D ≪≫ Functor.associator _ _ _ ≪≫ asIso εP ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft P.ι eH.symm ≪≫
        (Functor.associator _ _ _).symm
  obtain ⟨α, _, _⟩ :=
    (integralScalarExtensionWellDefined l E L ι X).2.choose_spec.choose_spec.2.2.1 D eD
  let eT : T ≅ D := α
  letI : T.CommShift ℤ := Functor.CommShift.ofIso eT.symm ℤ
  letI : NatTrans.CommShift eT.symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility eT.symm ℤ
  letI : T.IsTriangulated := Functor.isTriangulated_of_iso eT.symm
  exact ⟨inferInstance, inferInstance⟩

end WeilConjectures.IntegralFiniteExtension
