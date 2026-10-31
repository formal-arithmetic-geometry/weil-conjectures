/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerReconstructionData
import all WeilConjectures.AlgebraicGeometry.ConstantPrincipalCompleteOrthogonality
import WeilConjectures.AlgebraicGeometry.PrincipalIdealLocalTestCriterion
import WeilConjectures.AlgebraicGeometry.LocalCompletenessModels
import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import WeilConjectures.CategoryTheory.RingedIdealGenerators
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.CategoryTheory.RingedDerivedRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.CategoryTheory.RingedSiteCompleteElement
import WeilConjectures.CategoryTheory.RingedSiteLocalization
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.LocalCoefficientLocalization
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
import WeilConjectures.CategoryTheory.SliceAwayLocalizationFreeResolution
import WeilConjectures.CategoryTheory.SliceAwayLocalization
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementsIdeal
import Mathlib.RingTheory.Ideal.Span
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementMultiplication
import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestrictionSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import WeilConjectures.Algebra.Homology.HomTensorTotal
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexSupplement
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlatSupplement
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementAddition
import WeilConjectures.CategoryTheory.RingedSiteLocalizationCech
import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.RingTheory.TwoLocalizationExact
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementsLocal
import WeilConjectures.CategoryTheory.UnitPowerCompleteness
import all WeilConjectures.AlgebraicGeometry.IntegralScalarInternalHomComplete

/-! # Derived completeness of a coefficient tower limit

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, completeness sentence.
(blueprint: lem-sp-tower-limit-derived-complete)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite SheafOfModules
private theorem nsmul_hom_zero {A : Type*} [Category A] [Preadditive A]
    (n k : ℕ) {V X : A} [IsIso (n • 𝟙 V)]
    (hX : n ^ k • 𝟙 X = 0) (f : V ⟶ X) : f = 0 := by
  have hi (j : ℕ) : IsIso (n ^ j • 𝟙 V) := by
    induction j with
    | zero => simpa using (inferInstance : IsIso (𝟙 V))
    | succ j ih =>
      have : IsIso (n ^ j • 𝟙 V) := ih
      have he : n ^ (j + 1) • 𝟙 V = (n ^ j • 𝟙 V) ≫ (n • 𝟙 V) := by
        simp [Nat.pow_succ, smul_smul, Nat.mul_comm]
      rw [he]
      infer_instance
  have := hi k
  apply (cancel_epi (n ^ k • 𝟙 V)).mp
  rw [comp_zero, Preadditive.nsmul_comp, Category.id_comp,
    ← Category.comp_id f, ← Preadditive.comp_nsmul, hX, comp_zero]

private theorem limit_nsmul_orthogonal {A : Type*} [Category A] [HasZeroObject A]
    [HasShift A ℤ] [Preadditive A] [∀ j : ℤ, (shiftFunctor A j).Additive]
    [Pretriangulated A] (n : ℕ) (X : ℕ → A) [HasProduct X]
    (t : ∀ i, X (i + 1) ⟶ X i) (M : A) (p : M ⟶ ∏ᶜ X)
    (δ : (∏ᶜ X) ⟶ M⟦(1 : ℤ)⟧) (hlim : IsDerivedLimitTriangle t M p δ)
    (hX : ∀ i, ∃ k : ℕ, n ^ k • 𝟙 (X i) = 0)
    (V : A) [IsIso (n • 𝟙 V)] (f : V ⟶ M) : f = 0 := by
  have ht : Triangle.mk p (towerTransitionEndomorphism t) δ ∈ distTriang A := hlim
  have h₀ : f ≫ p = 0 := by
    apply Pi.hom_ext
    intro i
    rw [zero_comp]
    obtain ⟨k, hk⟩ := hX i
    exact nsmul_hom_zero n k hk _
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₁
    (Triangle.mk p (towerTransitionEndomorphism t) δ) ht (f⟦(1 : ℤ)⟧')
    (by
      dsimp only [Triangle.mk]
      rw [← Functor.map_comp, h₀, Functor.map_zero])
  have hV : IsIso (n • 𝟙 (V⟦(1 : ℤ)⟧)) := by
    rw [← CategoryTheory.Functor.map_id (shiftFunctor A (1 : ℤ)), ← Functor.map_nsmul]
    infer_instance
  have hg₀ : g = 0 := by
    apply Pi.hom_ext
    intro i
    rw [zero_comp]
    obtain ⟨k, hk⟩ := hX i
    exact nsmul_hom_zero n k hk _
  rw [hg₀, zero_comp] at hg
  exact (shiftFunctor A (1 : ℤ)).map_eq_zero_iff.mp hg

namespace CategoryTheory.ConstantCompletion
attribute [local instance] HasDerivedCategory.standard

private theorem principal_complete_of_nsmul_orthogonal
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (n : ℕ)
    (a b v : (R.obj ⋙ forget CommRingCat).sections) (e : ℕ)
    (ha : ∀ U, a.val U = (n : R.obj.obj U))
    (hv : ∀ U, IsUnit (v.val U)) (he : 1 ≤ e)
    (hab : ∀ U, a.val U = v.val U * b.val U ^ e)
    (M : D R)
    (hM : ∀ V : D R, IsIso (n • 𝟙 V) → Subsingleton (V ⟶ M)) :
    principalLocallyComplete.{u, u, u, u+1} R b M := by
  have hgen (U : C) : IsRingedSiteCompleteElement J R M U (a.val (op U)) := by
    apply (localCompleteness_models_iff J R M U _).mp
    let s := ringedSliceSection R U (a.val (op U))
    have hi := localization_nsmul_iso (J.over U) (R.over U) n s (by
      intro X
      refine ⟨1, ?_⟩
      change R.obj.map X.unop.hom.op (a.val (op U)) = _
      rw [ha, map_natCast, mul_one])
    let L := (DerivedCategory.singleFunctor (Mod (R.over U)) 0).obj
      (ringedSectionLocalization (R.over U) s)
    have hL : IsIso (n • 𝟙 L) := by
      have := hi
      rw [show n • 𝟙 L = (DerivedCategory.singleFunctor (Mod (R.over U)) 0).map
        (n • 𝟙 (ringedSectionLocalization (R.over U) s)) by
          rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]]
      infer_instance
    exact hom_zero_of_orthogonal (J.over U) (R.over U) n _ L
      (restricted_orthogonal J R n M hM U) hL
  have hc : principalLocallyComplete.{u, u, u, u+1} R a M := by
    obtain ⟨I, hI, _, hlocal, _⟩ := ringedSite_complete_elements_ideal J R M
    intro U s hs
    rw [principalSliceSection_eta R U s]
    apply (localCompleteness_models_iff J R M U _).mpr
    apply (hI U _).mp
    obtain ⟨S, hS, hs⟩ := hs
    apply hlocal U S hS
    intro V f hf
    obtain ⟨c, hc⟩ := hs V f hf
    have hn := s.property (show op (Over.mk (𝟙 U)) ⟶ op (Over.mk f) from
      (Over.homMk f (by simp)).op)
    change R.obj.map f.op (s.val (op (Over.mk (𝟙 U)))) = s.val (op (Over.mk f)) at hn
    rw [hn, hc]
    exact Ideal.mul_mem_right _ _ ((hI V _).mpr (hgen V))
  apply (principalLocallyComplete_iff R b M).mpr
  exact ((unit_power_localDerivedComplete R a b v e hv he hab).1 M).mp
    ((principalLocallyComplete_iff R a M).mp hc)
end CategoryTheory.ConstantCompletion

namespace AlgebraicGeometry.ProEtale

attribute [-instance] spCoefficientModulesAbelian
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
  (D : SpCoefficientTowersAbelian l E T)

private theorem spFiniteLevel_nsmul_zero (n : ℕ)
    (N : SheafOfModules.{u + 1} (spCoefficientRing.{u, u} l E T n)) :
    l ^ (n + 1) • 𝟙 N = 0 := by
  let : HasSheafify (Scheme.ProEt.topology T) CommRingCat.{u+1} :=
    WeilConjectures.integralCoefficientRingSheafify.{u, u} T
  have hz : (l ^ (n + 1) : ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1))) = 0 := by
    apply ULift.ext
    change (l ^ (n + 1) :
      Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1)) = 0
    have h₀ : (Ideal.Quotient.mk (spEllIdeal l E ^ (n + 1)))
        ((l : Padic.coefficientExtensionIntegers l E) ^ (n + 1)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) (n + 1))
    simpa only [map_pow, map_natCast] using h₀
  have hzU (U : T.ProEtᵒᵖ) :
      (l ^ (n + 1) : (spCoefficientRing.{u, u} l E T n).obj.obj U) = 0 := by
    let q : ULift.{u+1}
        (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1)) →+*
        (spCoefficientRing.{u, u} l E T n).obj.obj U :=
      ((toSheafify (D := CommRingCat.{u+1}) (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1)))))).app U).hom
    have h := congrArg q hz
    simpa only [map_pow, map_natCast, map_zero] using h
  apply (SheafOfModules.forget (spCoefficientRing.{u, u} l E T n)).map_injective
  simp only [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
  apply PresheafOfModules.hom_ext
  intro U
  let F := PresheafOfModules.evaluation (spCoefficientRing.{u, u} l E T n).obj U
  change F.map (l ^ (n + 1) • 𝟙 N.val) = F.map 0
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.hom_nsmul, ModuleCat.hom_id, ModuleCat.hom_zero,
    LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply]
  rw [← Nat.cast_smul_eq_nsmul ((spCoefficientRing.{u, u} l E T n).obj.obj U),
    Nat.cast_pow, hzU, zero_smul]

private theorem spCompletedLevel_nsmul_zero (n : ℕ)
    (C : spDerivedCoefficientTowers l E T D) :
    l ^ (n + 1) • 𝟙 ((spDerivedCompletedEvaluation l E T D n).obj C) = 0 := by
  let := D.hasDerived
  let P := DerivedCategory.Q.objPreimage C
  let e := (spDerivedCompletedEvaluation l E T D n).mapIso
      (DerivedCategory.Q.objObjPreimageIso C).symm ≪≫
    (spCompletedEvaluationFactors l E T D n).app P
  have hc : l ^ (n + 1) • 𝟙
      (((spCompletedEvaluation l E T D n).mapHomologicalComplex (.up ℤ)).obj P) = 0 := by
    apply HomologicalComplex.hom_ext
    intro q
    change l ^ (n + 1) • 𝟙 ((spCompletedEvaluation l E T D n).obj (P.X q)) = 0
    have h := spFiniteLevel_nsmul_zero l E T n
      ((spCoefficientEvaluation l E T D.equivalence n).obj (P.X q))
    change l ^ (n + 1) • 𝟙
      ((spCompletedEllRestriction l E T n).obj
        ((spCoefficientEvaluation l E T D.equivalence n).obj (P.X q))) = 0
    simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] using
      congrArg (spCompletedEllRestriction l E T n).map h
  have hd : l ^ (n + 1) • 𝟙 (DerivedCategory.Q.obj
      (((spCompletedEvaluation l E T D n).mapHomologicalComplex (.up ℤ)).obj P)) = 0 := by
    simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] using
      congrArg DerivedCategory.Q.map hc
  apply (cancel_mono e.hom).mp
  rw [zero_comp, Preadditive.nsmul_comp, Category.id_comp,
    ← Category.comp_id e.hom, ← Preadditive.comp_nsmul]
  change e.hom ≫ (l ^ (n + 1) • 𝟙 (DerivedCategory.Q.obj
    (((spCompletedEvaluation l E T D n).mapHomologicalComplex (.up ℤ)).obj P))) = 0
  rw [hd, comp_zero]

private def spScalarRingHom (U : T.ProEtᵒᵖ) :
    Padic.coefficientExtensionIntegers l E →+*
      (WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E T).obj.obj U := by
  letI : HasSheafify (Scheme.ProEt.topology T) CommRingCat.{u+1} :=
    WeilConjectures.integralCoefficientRingSheafify.{u, u} T
  exact
    ((WeilConjectures.integralConstantToCompletionOfUniverses.{u, u} l E T).hom.app U).hom.comp
      (((toSheafify (D := CommRingCat.{u+1}) (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (CommRingCat.of.{u+1} (ULift.{u+1} (Padic.coefficientExtensionIntegers l E))))).app
            U).hom.comp ULift.ringEquiv.{u, u+1}.symm.toRingHom)

private theorem spComplete_of_orthogonal
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    (hM : ∀ V, IsIso (l • 𝟙 V) → Subsingleton (V ⟶ M)) :
    WeilConjectures.IsSfDerivedComplete l E T M := by
  let J := Scheme.ProEt.topology T
  let R := WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E T
  let Rg := (sheafCompose J (forget₂ CommRingCat.{u+1} RingCat.{u+1})).obj R
  let a : (R.obj ⋙ forget CommRingCat).sections :=
    ⟨(spCompletedScalar.{u, u} l E T l).val, (spCompletedScalar.{u, u} l E T l).property⟩
  let b : (R.obj ⋙ forget CommRingCat).sections :=
    ⟨(spCompletedScalar.{u, u} l E T (Padic.coefficientExtensionUniformizer l E)).val,
      (spCompletedScalar.{u, u} l E T (Padic.coefficientExtensionUniformizer l E)).property⟩
  obtain ⟨e, v, he, hell⟩ := (sp_completed_coefficients_regular.{u, u} l E T).1
  let z : (R.obj ⋙ forget CommRingCat).sections :=
    ⟨(spCompletedScalar.{u, u} l E T (v : Padic.coefficientExtensionIntegers l E)).val,
      (spCompletedScalar.{u, u} l E T (v : Padic.coefficientExtensionIntegers l E)).property⟩
  have ha (U : T.ProEtᵒᵖ) : a.val U = (l : R.obj.obj U) := by
    with_unfolding_all
      dsimp only [a, spCompletedScalar, PresheafOfModules.sectionsMk]
      change spScalarRingHom l E T U (l : Padic.coefficientExtensionIntegers l E) = _
      exact map_natCast _ l
  have hv (U : T.ProEtᵒᵖ) : IsUnit (z.val U) := by
    with_unfolding_all
      dsimp only [z, spCompletedScalar, PresheafOfModules.sectionsMk]
      exact v.isUnit.map (spScalarRingHom l E T U)
  have hab (U : T.ProEtᵒᵖ) : a.val U = z.val U * b.val U ^ e := by
    with_unfolding_all
      dsimp only [a, z, b, spCompletedScalar, PresheafOfModules.sectionsMk]
      change spScalarRingHom l E T U (l : Padic.coefficientExtensionIntegers l E) =
        spScalarRingHom l E T U (v : Padic.coefficientExtensionIntegers l E) *
          spScalarRingHom l E T U (Padic.coefficientExtensionUniformizer l E) ^ e
      simpa only [map_mul, map_pow] using congrArg (spScalarRingHom l E T U) hell
  let : HasSheafify J AddCommGrpCat.{u+1} :=
    WeilConjectures.IntegralOnSlice.abSheafify.{u, u} T none
  let : J.WEqualsLocallyBijective AddCommGrpCat.{u+1} :=
    WeilConjectures.IntegralOnSlice.abLocallyBijective.{u, u} T none
  let : ∀ U : T.ProEt, HasSheafify (J.over U) AddCommGrpCat.{u+1} :=
    fun U ↦ WeilConjectures.IntegralOnSlice.abSheafify.{u, u} T (some U)
  let : ∀ U : T.ProEt, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u+1} :=
    fun U ↦ WeilConjectures.IntegralOnSlice.abLocallyBijective.{u, u} T (some U)
  let : ∀ U : T.ProEt, HasSheafify (J.over U) CommRingCat.{u+1} := fun U ↦
    letI : EssentiallySmall.{u+1} (Over U) := essentiallySmallSelf.{0, u, u+1} _
    hasSheafifyEssentiallySmallSite.{u, u+1, u+1} _ _
  let : ∀ U : T.ProEt, HasDerivedCategory (SheafOfModules.{u+1} (Rg.over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let F := AsSmall.down.{u, u+1, u+1} (C := T.ProEt)
  let Js := F.inducedTopology J
  let : F.IsEquivalence :=
    (AsSmall.equiv.{u, u+1, u+1} (C := T.ProEt)).symm.isEquivalence_functor
  let S := NativeRestriction.restrictedCommRing.{u+1, u+1, u+1, u, u} (K := Js) F R
  let H := NativeRestriction.restrictModules.{u+1, u+1, u+1, u, u} (K := Js) F R
  let : H.IsEquivalence := NativeRestriction.globalModulesEquivalence (K := Js) F R
  let : HasDerivedCategory (NativeRestriction.NativeModules.{u+1, u+1, u+1} S) :=
    HasDerivedCategory.standard _
  let Rs := NativeRestriction.NativeRings.{u+1, u+1, u+1} S
  let : ∀ U : AsSmall.{u+1} T.ProEt,
      HasDerivedCategory (SheafOfModules.{u+1} (Rs.over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let G := H.mapDerivedCategory
  have ho (V : DerivedCategory (NativeRestriction.NativeModules.{u+1, u+1, u+1} S))
      (hV : IsIso (l • 𝟙 V)) : Subsingleton (V ⟶ G.obj M) := by
    let V₀ := G.objPreimage V
    let i := G.objObjPreimageIso V
    have hi : IsIso (l • 𝟙 (G.obj V₀)) := by
      have := hV
      have hh : l • 𝟙 (G.obj V₀) = i.hom ≫ (l • 𝟙 V) ≫ i.inv := by
        dsimp only [V₀]
        simp
      rw [hh]
      infer_instance
    have hi₀ : IsIso (l • 𝟙 V₀) := by
      have him : IsIso (G.map (l • 𝟙 V₀)) := by
        simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id] using hi
      exact isIso_of_reflects_iso _ G
    have := hM V₀ hi₀
    refine ⟨fun f g ↦ ?_⟩
    apply (cancel_epi i.hom).mp
    exact (G.map_preimage (i.hom ≫ f)).symm.trans
      ((congrArg G.map (Subsingleton.elim (G.preimage (i.hom ≫ f))
        (G.preimage (i.hom ≫ g)))).trans (G.map_preimage (i.hom ≫ g)))
  let a' := NativeRestriction.restrictedSection.{u+1, u+1, u+1, u, u} (K := Js) F R a
  let b' := NativeRestriction.restrictedSection.{u+1, u+1, u+1, u, u} (K := Js) F R b
  let z' := NativeRestriction.restrictedSection.{u+1, u+1, u+1, u, u} (K := Js) F R z
  have hc := CategoryTheory.ConstantCompletion.principal_complete_of_nsmul_orthogonal
    Js S l a' b' z' e (fun U ↦ ha (F.op.obj U))
    (fun U ↦ hv (F.op.obj U)) he (fun U ↦ hab (F.op.obj U)) (G.obj M) ho
  have hn : principalLocallyComplete.{u+1, u, u, u+2} R b M :=
    (NativeRestriction.smallModelComplete.{u+1, u, u, u+2} R b M).mpr hc
  apply (WeilConjectures.scalarSfLocalIff l E T M).mpr
  intro U s hs
  have hz := hn U s hs
  let := (SheafOfModules.overFunctor_exact_ofUniverses Rg U).1
  let := (SheafOfModules.overFunctor_exact_ofUniverses Rg U).2
  let i : WeilConjectures.IntegralPrincipalCone.localTest l E T M U s ≅
      principalLocalTest.{u+1, u, u, u+2} R M U s :=
    (WeilConjectures.IntegralOnSlice.hom l E T (some U)).mapIso
      ((Iso.refl _).prod (SheafOfModules.overFunctor_derivedRestrictionIso Rg U M))
  exact hz.of_iso i

/-- Completeness of any derived coefficient-tower limit. Neither normalization nor
constructibility is needed.
Source: current blueprint, sk-lem-sp-tower.proof.md, sentence "The complex C is
derived complete as a limit of complexes killed by powers of ell"; Bhatt--Scholze,
Lemmas 3.5.4--3.5.7 (blueprint: lem-sp-tower-limit-derived-complete).

Proof: the finite coefficient ring at level n has ell^(n+1)=0. Sheafification,
restriction of scalars and exact derived evaluation preserve this annihilation.
A morphism from an ell-invertible object to such a level is zero: precomposition
with ell^(n+1) is invertible, while postcomposition with it is zero. Products
preserve this vanishing. Apply triangle exactness also to the shifted source to
obtain the same orthogonality for M.

Pass to the equivalent small ringed site. Extension by zero from every slice
preserves ell-invertibility. Tensor-Hom adjunction therefore makes the internal
Hom from each ell-localized rank-one object vanish. The complete-elements ideal
and its covering-sieve descent extend the generator test to all locally divisible
sections. Write ell=v*pi^e with v a unit and e positive; the unit-power comparison
identifies this completeness with uniformizer completeness. Transfer back from
the small site and apply the existing comparison with the specified quotient
completion unit. This gives exactly IsSfDerivedComplete M, without boundedness,
normalization, or a common torsion exponent. -/
theorem spTower_limit_derived_complete
    (C : spDerivedCoefficientTowers l E T D)
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    [HasProduct (fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C)
    (δ : (∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C) ⟶ M⟦(1 : ℤ)⟧)
    (hlim : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (spDerivedCompletedTransition l E T D n).app C) M p δ) :
    WeilConjectures.IsSfDerivedComplete l E T M := by
  have horth (V : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
      (hV : IsIso (l • 𝟙 V)) : Subsingleton (V ⟶ M) := by
    have := hV
    refine ⟨fun f g ↦ ?_⟩
    have hz (f : V ⟶ M) : f = 0 :=
      limit_nsmul_orthogonal l _ _ M p δ hlim
        (fun n ↦ ⟨n + 1, spCompletedLevel_nsmul_zero l E T D n C⟩) V f
    exact (hz f).trans (hz g).symm
  exact spComplete_of_orthogonal l E T M horth

end AlgebraicGeometry.ProEtale
