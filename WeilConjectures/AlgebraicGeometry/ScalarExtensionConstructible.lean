/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.RestrictedScalarCohomologyLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.FiniteFreeApproximationHomology
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import all WeilConjectures.AlgebraicGeometry.Restricted.RestrictedScalarCoefficientLocalConstancy
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteUnderlyingModels
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteActionLocalModels
import all WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Finite scalar extension preserves constructible cohomology

Source: Stacks 06YY, 0944, and current scalar-extension clause (2), bpq #46.
(blueprint: lem-sp-finite-scalar-constructibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u cv cu cw
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

private theorem scalarFiniteSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
attribute [-instance] proEtaleRingModules_hasDerivedCategory
attribute [local instance] scalarFiniteSmall HasDerivedCategory.standard
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientRingSheafify

private theorem scalarFinite_coefficientIso (T : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    Nonempty ((commutativeSiteConstantModuleFunctor (ProEt.topology T)
      (ULift.{u + 1, u} A)).obj (coefficientModel f) ≅ coefficientModule T f) := by
  let J := ProEt.topology T
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing T A)
  let a := proEtaleModuleScalarUnit T A
  have : Presheaf.IsLocallyInjective J a :=
    (proEtaleConstantRingUnit_locallyBijective T A).1
  have : Presheaf.IsLocallySurjective J a :=
    (proEtaleConstantRingUnit_locallyBijective T A).2
  obtain ⟨e⟩ := coefficientRestrictionIso T f
  have := ConstantScalarComparison.constantComparisonHom_isIso.{u} J
    (ULift.{u + 1, u} A) R a (coefficientModel f)
  exact ⟨(ConstantScalarComparison.restrictionFullyFaithful.{u} J
    (ULift.{u + 1, u} A) R a).preimageIso
      ((asIso (ConstantScalarComparison.constantComparisonHom.{u} J
        (ULift.{u + 1, u} A) R a (coefficientModel f))).symm ≪≫ e)⟩

/-- Finite coefficient extension has constructible cohomology in every degree.
Source: Stacks 06YY and 0944; current scalar extension (2), bpq #46
(blueprint: lem-sp-finite-scalar-constructibility).
Proof: resolve B over the finite Noetherian ring A by finite free modules. Brutal
truncations give bounded finite-free approximations with arbitrarily low error cone.
The exact constant realization followed by tensor with K carries the error below the
chosen cohomology degree. The finite iterated cones of finite sums of shifts of K have
constructible cohomology. Thus the tensor with B has constructible A-cohomology in each
degree. Its underlying sets agree with scalar extension; finite B-actions refine the
finite local models on each stratum to B-module models. No Noetherian scheme or common
stratification for all the cohomology of K is used. -/
theorem finiteScalarExtension_constructible
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (K : proEtaleDerivedCategory T A)
    (hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K)})
    (hconstructible : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj K)) :
    ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T B
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T B)) i).obj
          ((constantCoefficientScalarExtensionOfUniverses.{u + 1, u, u + 1, u + 2, u + 2}
            (ProEt.topology T) (RingHom.ulift f)).obj K)) := by
  classical
  let R := proEtaleConstantRing T A
  let C := proEtaleRingModules T R
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  let := SheafOfModules.hasFunctorialFlatResolution_kfi R
  have : IsGrothendieckAbelian.{u + 1} C :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      (ProEt.topology T) _
  have : ∀ X Y : GradedObject ℤ C, GradedObject.HasTensor X Y := by infer_instance
  have : ∀ X Y Z : GradedObject ℤ C,
      GradedObject.HasGoodTensor₁₂Tensor X Y Z := by infer_instance
  have : ∀ X Y Z : GradedObject ℤ C,
      GradedObject.HasGoodTensorTensor₂₃ X Y Z := by infer_instance
  have : ∀ X Y Z W : GradedObject ℤ C,
      GradedObject.HasTensor₄ObjExt X Y Z W := by infer_instance
  have : DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (.up ℤ)) := by infer_instance
  let Λ := ULift.{u + 1, u} A
  let c := commutativeSiteConstantModuleFunctor (ProEt.topology T) Λ
  let F := c.mapDerivedCategory ⋙ tensorLeft K
  let BC : ObjectProperty (DerivedCategory C) := fun L ↦
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor C i).obj L)} ∧
    ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor C i).obj L)
  have hBC := proEtale_bounded_constructible_isTriangulated T A
  let : BC.IsClosedUnderIsomorphisms := hBC.1
  let : BC.IsTriangulated := hBC.2
  have hK : BC K := ⟨hbounded, hconstructible⟩
  obtain ⟨b, hb⟩ := hbounded.bddAbove
  have hKb : K.IsLE b := (DerivedCategory.isLE_iff K b).2 (fun i hi ↦ by
    by_contra hz
    exact (not_le_of_gt hi) (hb hz))
  let := hKb
  have hbound (N : DerivedCategory (ModuleCat.{u + 1} Λ)) (j : ℤ) (hj : N.IsLE j) :
      (F.obj N).IsLE (j + b) := by
    let := hj
    have : (c.mapDerivedCategory.obj N).IsLE j := c.isLE_mapDerivedCategory_obj N j
    have h := DerivedCategory.isLE_tensor K (c.mapDerivedCategory.obj N) b j
    change (K ⊗ c.mapDerivedCategory.obj N).IsLE (j + b)
    simpa only [add_comm b j] using h
  have hfree (M : ModuleCat.{u + 1} Λ) (i : ℤ)
      (hfr : Module.Free Λ M) (hfi : Module.Finite Λ M) :
      BC (F.obj ((DerivedCategory.singleFunctor _ i).obj M)) := by
    let := hfr
    let := hfi
    apply DerivedCategory.triangulatedImage_single_free Λ F BC
    obtain ⟨ereg⟩ := scalarFinite_coefficientIso T (RingHom.id A)
    have hi : restrictedScalarRingMap T (RingHom.id A) = 𝟙 R :=
      CategoryTheory.Functor.map_id (constantSheaf (ProEt.topology T) CommRingCat.{u + 1})
        (CommRingCat.of Λ)
    have eright : coefficientModule T (RingHom.id A) ≅ SheafOfModules.unit
        ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) := by
      unfold coefficientModule
      rw [hi, CategoryTheory.Functor.map_id]
      exact Iso.refl _
    have er : c.obj (ModuleCat.of Λ Λ) ≅ SheafOfModules.unit
        ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) := by
      exact ereg ≪≫ eright
    have eu : SheafOfModules.unit ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ≅ (𝟙_ C) := by
      with_unfolding_all exact Iso.refl _
    let ec : c.mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of Λ Λ)) ≅ (𝟙_ (DerivedCategory C)) :=
      (c.mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (er ≪≫ eu) ≪≫
          DerivedCategory.singleFunctorObjUnitIso C
    exact BC.prop_of_iso ((tensorLeft K).mapIso ec ≪≫ ρ_ K).symm hK
  have htensor (q : ℤ) : IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor C q).obj
        (F.obj ((DerivedCategory.singleFunctor _ 0).obj (coefficientModel f)))) := by
    have : Finite (coefficientModel f) := inferInstanceAs (Finite (ULift.{u + 1, u} B))
    have : Module.Finite Λ (coefficientModel f) := Module.Finite.of_finite
    have : Module.FinitePresentation Λ (coefficientModel f) :=
      Module.finitePresentation_of_finite Λ (coefficientModel f)
    obtain ⟨V, hV, ⟨e⟩⟩ := DerivedCategory.finiteModuleImage_homology_approximation Λ F BC b
      hbound hfree (coefficientModel f) q
    exact constructibleProEtale_of_iso T A e (hV.2 q)
  let D := Classical.choice (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel
    (restrictedScalarRingMap T f))
  change ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf T B
    ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T B)) q).obj (D.T.obj K))
  let G := DerivedCategory.Q.objPreimage K
  obtain ⟨P, p, hP, _hflat, hp, _hepi⟩ := CochainComplex.exists_isKFlatResolutionGeneral G
  have := hp
  let eK : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨ec⟩ := scalarFinite_coefficientIso T f
  let eF := (tensorLeft K).mapIso ((c.mapDerivedCategorySingleFunctor 0).app
    (coefficientModel f) ≪≫ (DerivedCategory.singleFunctor C 0).mapIso ec)
  obtain ⟨ep⟩ := scalarExtension_abstract_tensor_comparison P hP K eK (coefficientModule T f)
  let eT := ep ≪≫ eF.symm
  intro q
  have hZ : IsConstructibleProEtaleModuleSheaf T A
      (restrictedScalarTensorCohomology T f P hP q) :=
    constructibleProEtale_of_iso T A
      ((DerivedCategory.homologyFunctor C q).mapIso eT).symm (htensor q)
  obtain ⟨S, hn, hS⟩ := hZ
  refine ⟨S, hn, fun i ↦ scalarExtension_models_finiteLocal (S.domain i) B _ ?_⟩
  have hl : IsLocallyConstantProEtaleModuleSheafOfUniverses.{u, u} (S.domain i) A
      (proEtaleConstantModulePullback (S.immersion i) A
        (restrictedScalarTensorCohomology T f P hP q)) := by
    obtain ⟨I, U, g, hg, he⟩ := (hS i).1
    exact ⟨I, U, g, hg, fun j ↦ ⟨(he j).choose, trivial, (he j).choose_spec⟩⟩
  have hsets := proEtale_finiteUnderlyingModels_of_locallyConstant (S.domain i) A _ hl
    (hS i).2
  let V := sheafCompose (ProEt.topology (S.domain i))
    (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let e := V.mapIso ((SheafOfModules.toSheaf _).mapIso
    ((proEtaleConstantModulePullbackFunctor (S.immersion i) B).mapIso
      ((DerivedCategory.homologyFunctor _ q).mapIso (D.T.mapIso eK).symm))) ≪≫
        (restrictedScalarTensorCohomologyComparison (S.immersion i) f D P hP q).some
  apply proEtale_finiteLocalModels_of_finiteUnderlying (S.domain i) B
  intro U
  obtain ⟨Z, hZ, hs⟩ := hsets U
  refine ⟨Z, hZ, fun W g hg ↦ ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := hs W g hg
  exact ⟨M, hM, ⟨((ProEt.topology (S.domain i)).overPullback
    (Type (u + 1)) W).mapIso e ≪≫ eM⟩⟩

end AlgebraicGeometry.Scheme
