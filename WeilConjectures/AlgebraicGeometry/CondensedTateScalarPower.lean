/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedTateRealizationData
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsSequentialColimit
import WeilConjectures.AlgebraicGeometry.CompletedCondensedCoefficients
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Scalar extension of the integral Tate tensor powers

Source: Stacks 03EK, 06YU, 0G7E and 07A4; Bhatt--Scholze 6.8.4.
(blueprint: lem-route-scalar-balanced-power-is-iso)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures WeilConjectures.CondensedERealization

namespace AlgebraicGeometry.ProEtale.CondensedTateRealization

variable (l : ℕ) [Fact l.Prime]

attribute [local instance] At.encodingAdditive

open CategoryTheory.MonObj
open scoped CategoryTheory.Obj

attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
  Mod.extendScalars Mod.monoidalClosed DerivedCategory.monoidalClosed
  integralComparison moduleEncoding integralEncoding upperStarFromPoint

attribute [local implicit_reducible] integralPower tateTwistNat tateTwistOne

private theorem integralRational_exact (X : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (coefficientMap
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.padicIntCondensedRingToPadicCondensedRing l)) X)) := by
  obtain ⟨j, hj, _⟩ := completedCondensedPadicRational.{u} l
  let A := (completedCoefficient X (Profinite.padicIntCondensedRing l)).X
  let φ := (completedCoefficientMap X
    (Profinite.padicIntCondensedRingToPadicCondensedRing l)).hom
  have hc : ∀ n, l • j X (n + 1) = j X n := (hj X).2.2.1
  have hcol : IsColimit (Mod.smulSequenceCocone l (j X) hc) := by
    apply IsColimit.ofExistsUnique
    intro s
    apply (hj X).2.2.2 s.pt (fun n ↦ s.ι.app n)
    intro n
    have h := s.w (homOfLE (Nat.le_succ n))
    simpa only [Mod.smulSequence_map, Nat.succ_eq_add_one, Nat.add_sub_cancel_left, pow_one,
      Functor.const_obj_map, Category.comp_id, Preadditive.nsmul_comp,
      Category.id_comp] using h
  have : HasExactColimitsOfShape ℕ (Sheaf (ProEt.topology X) Ab.{u + 1}) := by
    have := AB5OfSize_of_univLE.{0, 0} (Sheaf (ProEt.topology X) Ab.{u + 1})
    infer_instance
  have hcol' := Mod.isColimitSmulSequenceCoconeMap (Mod.forget A) hc hcol
  have : IsCommMonObj A := by
    change IsCommMonObj (R X l)
    infer_instance
  have hnc : ∀ n, l • (j X (n + 1)).hom = (j X n).hom := by
    intro n
    simpa only [Mod.nsmul_hom] using congrArg Mod.Hom.hom (hc n)
  exact Mod.preservesFiniteLimits_extendScalars_of_isColimit
    (φ := φ) (c := fun n ↦ (j X n).hom) hnc hcol' (hj X).2.1

private theorem rationalLift_isIso : IsIso (rationalLiftRingMap.{u} l) := by
  refine ⟨⟨rationalDownRingMap l, ?_, ?_⟩⟩
  all_goals
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    apply ConcreteCategory.hom_ext
    intro f
    rfl

private theorem integralClosure_exact (X : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (integralToQbar X l)) := by
  let F := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})) ⋙ upperStarFromPoint X
  let a : R X l ⟶ condensedRingObj (Profinite.continuousMapRingObj ℚ_[l]) X :=
    F.map (Profinite.padicIntCondensedRingToPadicCondensedRing l)
  let b : condensedRingObj (Profinite.continuousMapRingObj ℚ_[l]) X ⟶
      Coefficient (LiftedQ.{u} l) X := F.map (rationalLiftRingMap l)
  let c := rationalToQbar X l
  have : IsIso b := by
    have := rationalLift_isIso.{u} l
    exact Functor.map_isIso F _
  have : IsMonHom a := by dsimp [a, F]; infer_instance
  have : IsMonHom b := by dsimp [b, F]; infer_instance
  have : PreservesFiniteLimits (Mod.extendScalars a) := integralRational_exact l X
  have : PreservesFiniteLimits (Mod.extendScalars b) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv b).symm
  have : PreservesFiniteLimits (Mod.extendScalars c) := rationalToQbar_preservesFiniteLimits X l
  have : PreservesFiniteLimits (Mod.extendScalars a ⋙ Mod.extendScalars b) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (Mod.extendScalars (a ≫ b)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsComp a b).symm
  have : PreservesFiniteLimits (Mod.extendScalars (a ≫ b) ⋙ Mod.extendScalars c) :=
    comp_preservesFiniteLimits _ _
  have h : (a ≫ b) ≫ c = integralToQbar X l := by
    change (F.map _ ≫ F.map _) ≫ F.map _ = F.map _
    rw [← F.map_comp, ← F.map_comp]
    rfl
  exact preservesFiniteLimits_of_natIso
    ((Mod.extendScalarsIsoOfEq h.symm) ≪≫ Mod.extendScalarsComp (a ≫ b) c).symm

section TensorAdjunction

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ M : C, PreservesColimitsOfSize.{0, 0} (tensorLeft M)]
  [∀ M : C, PreservesColimitsOfSize.{0, 0} (tensorRight M)]
  {A B : C} [MonObj A] [MonObj B] [IsCommMonObj A] [IsCommMonObj B]

-- These tensor formulas need the chosen monoidal data inlined during rewriting.
set_option linter.style.haveILetI false in
attribute [local semireducible] Mod.extendScalars in
private theorem extensionTensor_transpose (φ : A ⟶ B) [IsMonHom φ]
    {M N : Mod C A} {M' N' : Mod C B}
    (f : (Mod.extendScalars φ).obj M ⟶ M')
    (g : (Mod.extendScalars φ).obj N ⟶ N') :
    letI := Mod.extendScalarsMonoidal φ
    (Mod.extendRestrictAdjunction φ).homEquiv _ _
        (Functor.OplaxMonoidal.δ (Mod.extendScalars φ) M N ≫ (f ⊗ₘ g)) =
      ((Mod.extendRestrictAdjunction φ).homEquiv _ _ f ⊗ₘ
        (Mod.extendRestrictAdjunction φ).homEquiv _ _ g) ≫
          Mod.comapTensorHom φ M' N' := by
  letI := Mod.comapLaxMonoidal φ
  letI := Mod.extendScalarsMonoidal φ
  let a := Mod.extendRestrictAdjunction φ
  rw [Adjunction.homEquiv_naturality_right]
  erw [Mod.extendScalarsOplaxMonoidal_δ]
  have he : (Mod.extendRestrictAdjunction φ).homEquiv = Mod.extendHomEquiv φ :=
    Adjunction.mkOfHomEquiv_homEquiv _
  rw [he]
  erw [Equiv.apply_symm_apply]
  rw [← he]
  change ((Mod.extendUnit φ M ⊗ₘ Mod.extendUnit φ N) ≫
      Functor.LaxMonoidal.μ (Mod.comap φ) _ _) ≫ (Mod.comap φ).map (f ⊗ₘ g) = _
  rw [Category.assoc]
  erw [← Functor.LaxMonoidal.μ_natural]
  erw [← Category.assoc, ← tensorHom_comp_tensorHom]
  simp only [Mod.extendRestrictAdjunction_unit_app]
  rfl

set_option linter.style.haveILetI false in
attribute [local semireducible] Mod.extendScalars in
private theorem extensionTensor_underlying_unit (φ : A ⟶ B) [IsMonHom φ]
    {M N : Mod C A} {P : Mod C B}
    (f : (Mod.extendScalars φ).obj M ⟶ P) :
    letI := Mod.extendScalarsMonoidal φ
    Mod.tensorObjπ M N ≫
        ((Mod.extendRestrictAdjunction φ).homEquiv _ _
          (Functor.OplaxMonoidal.δ (Mod.extendScalars φ) M N ≫ (f ⊗ₘ 𝟙 _))).hom =
      (((Mod.extendRestrictAdjunction φ).homEquiv _ _ f).hom ⊗ₘ
        ((Mod.extendRestrictAdjunction φ).unit.app N).hom) ≫
          Mod.tensorObjπ P ((Mod.extendScalars φ).obj N) := by
  letI := Mod.extendScalarsMonoidal φ
  rw [extensionTensor_transpose, Adjunction.homEquiv_id]
  rw [Mod.comp_hom']
  erw [Mod.tensorObjπ_tensorHom_hom_whisker_assoc,
    Mod.tensorObjπ_comapTensorHom_hom]
  erw [MonoidalCategory.tensorHom_def, Category.assoc]
  rfl

end TensorAdjunction

private def ordinaryPowerIso (X : Scheme.{u}) : ∀ d : ℕ,
    (Mod.extendScalars (integralToQbar X l)).obj (integralPower X l d) ≅
      tateTwistNat X l d
  | 0 => by
      letI := Mod.extendScalarsMonoidal (integralToQbar X l)
      exact (Functor.Monoidal.εIso _).symm
  | d + 1 => by
      letI := Mod.extendScalarsMonoidal (integralToQbar X l)
      exact (Functor.Monoidal.μIso _ (integralPower X l d) (tateModule X l)).symm ≪≫
        (ordinaryPowerIso X d ⊗ᵢ Iso.refl (tateTwistOne X l))

private theorem ordinaryPowerIso_family (X : Scheme.{u}) :
    IsBalancedPowerFamily X l (fun d ↦
      (Mod.extendRestrictAdjunction (integralToQbar X l)).homEquiv _ _
        (ordinaryPowerIso l X d).hom) := by
  let φ := integralToQbar X l
  let F := Mod.extendScalars φ
  let G : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X) ⥤ IntegralModules X l := Mod.comap φ
  let a := Mod.extendRestrictAdjunction φ
  let := Mod.comapLaxMonoidal φ
  let := Mod.extendScalarsMonoidal φ
  refine ⟨?_, ?_⟩
  · change (a.homEquiv _ _ (Functor.OplaxMonoidal.η F)).hom = φ
    erw [Mod.extendScalarsOplaxMonoidal_η]
    change (Mod.extendHomEquiv φ _ _ (Mod.extendHom φ (Mod.comapUnitHom φ))).hom = φ
    erw [Equiv.apply_symm_apply]
    rfl
  · intro d
    change Mod.tensorObjπ (integralPower X l d) (tateModule X l) ≫
        (a.homEquiv _ _ (Functor.OplaxMonoidal.δ F _ _ ≫
          ((ordinaryPowerIso l X d).hom ⊗ₘ 𝟙 _))).hom = _
    exact extensionTensor_underlying_unit φ (ordinaryPowerIso l X d).hom

private theorem ordinaryPowerIso_transpose (X : Scheme.{u}) (d : ℕ) :
    (Mod.extendRestrictAdjunction (integralToQbar X l)).homEquiv _ _
      (ordinaryPowerIso l X d).hom = balancedPower X l d := by
  have h := (balancedPower_existsUnique X l).unique (ordinaryPowerIso_family l X)
    (balancedPower_existsUnique X l).exists.choose_spec
  exact congrFun h d


section ExactAdjunction

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

private def exactDerivedAdjunction (a : F ⊣ G) : F.mapDerivedCategory ⊣ G.mapDerivedCategory := by
  letI : CatCommSq (F.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso B (.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory

private theorem exactDerivedAdjunction_unit (a : F ⊣ G) (P : CochainComplex A ℤ) :
    (exactDerivedAdjunction a).unit.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        G.mapDerivedCategoryFactors.inv.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app P) := by
  dsimp only [exactDerivedAdjunction]
  rw [Adjunction.localization_unit_app]
  rfl

private theorem exactDerivedAdjunction_cochain (a : F ⊣ G)
    (P : CochainComplex A ℤ) (K : CochainComplex B ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ K) :
    (exactDerivedAdjunction a).homEquiv _ _
        (F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
        G.mapDerivedCategoryFactors.inv.app K := by
  rw [Adjunction.homEquiv_unit, exactDerivedAdjunction_unit, Functor.map_comp]
  simp only [Category.assoc]
  rw [← G.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  erw [G.mapDerivedCategory.map_id, Category.id_comp]
  erw [← G.mapDerivedCategoryFactors.inv.naturality]
  dsimp only [CategoryTheory.Functor.comp_map]
  rw [← DerivedCategory.Q.map_comp_assoc, Adjunction.homEquiv_unit]

private theorem exactDerivedAdjunction_single (a : F ⊣ G)
    (M : A) (N : B) (f : F.obj M ⟶ N) :
    (exactDerivedAdjunction a).homEquiv _ _
        ((F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
          (DerivedCategory.singleFunctor B 0).map f) =
      (DerivedCategory.singleFunctor A 0).map (a.homEquiv M N f) ≫
        (G.mapDerivedCategorySingleFunctor 0).inv.app N := by
  let P := (CochainComplex.singleFunctor A 0).obj M
  let K := (CochainComplex.singleFunctor B 0).obj N
  let cF := F.mapCochainComplexSingleFunctor 0
  let cG := G.mapCochainComplexSingleFunctor 0
  have hF : (F.mapDerivedCategorySingleFunctor 0).hom.app M =
      F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map (cF.hom.app M) := by
    erw [← F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app M]
    erw [Iso.hom_inv_id_app_assoc]
  have hc : (a.mapHomologicalComplex (.up ℤ)).homEquiv P K
      (cF.hom.app M ≫ (CochainComplex.singleFunctor B 0).map f) =
        (CochainComplex.singleFunctor A 0).map (a.homEquiv M N f) ≫ cG.inv.app N := by
    rw [Adjunction.homEquiv_unit]
    apply HomologicalComplex.Hom.ext
    funext i
    by_cases hi : i = 0
    · subst i
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        Adjunction.mapHomologicalComplex_unit_app_f, Functor.map_comp]
      dsimp only [P, cF, cG, Functor.mapCochainComplexSingleFunctor,
        CochainComplex.singleFunctor, CochainComplex.singleFunctors]
      simp only [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
        HomologicalComplex.single_map_f_self]
      erw [G.map_comp, G.map_comp, G.map_comp]
      erw [Category.assoc]
      erw [← reassoc_of% (a.unit.naturality
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom)]
      simp only [Adjunction.homEquiv_unit, ← G.map_comp_assoc]
      erw [← G.map_comp_assoc, Iso.inv_hom_id_assoc]
      repeat' erw [Category.assoc]
      erw [Iso.inv_hom_id_assoc]
      rfl
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi).eq_of_src _ _
  rw [hF]
  erw [Category.assoc]
  change (exactDerivedAdjunction a).homEquiv _ _
      (F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map (cF.hom.app M) ≫
        DerivedCategory.Q.map ((CochainComplex.singleFunctor B 0).map f)) = _
  rw [← DerivedCategory.Q.map_comp, exactDerivedAdjunction_cochain, hc,
    DerivedCategory.Q.map_comp, Category.assoc]
  change _ ≫ DerivedCategory.Q.map (cG.inv.app N) ≫
      G.mapDerivedCategoryFactors.inv.app K = _
  have hG := G.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app N
  apply congrArg (fun q ↦ (DerivedCategory.singleFunctor A 0).map
    (a.homEquiv M N f) ≫ q)
  apply (cancel_mono (G.mapDerivedCategoryFactors.hom.app K)).1
  erw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact hG.symm

end ExactAdjunction

open AlgebraicGeometry.ProEtale.CondensedRing

private def ringModuleSquare (X : Scheme.{u})
    {R S A B : Sheaf (ProEt.topology X) RingCat.{u + 1}}
    (e : S ≅ R) (b : B ≅ A) (a : S ⟶ B) (ψ : R ⟶ A)
    (h : e.inv ≫ a = ψ ≫ b.inv) :
    SheafOfModules.restrictScalars a ⋙ (ringModuleEquivalenceOfIso X e.symm).functor ≅
      (ringModuleEquivalenceOfIso X b.symm).functor ⋙
        SheafOfModules.restrictScalars ψ := by
  change SheafOfModules.restrictScalars a ⋙ SheafOfModules.restrictScalars e.inv ≅
    SheafOfModules.restrictScalars b.inv ⋙ SheafOfModules.restrictScalars ψ
  exact SheafOfModules.pushforwardComp (F := 𝟭 X.ProEt) (G := 𝟭 X.ProEt) e.inv a ≪≫
    SheafOfModules.pushforwardCongr h ≪≫
      (SheafOfModules.pushforwardComp (F := 𝟭 X.ProEt) (G := 𝟭 X.ProEt) ψ b.inv).symm

set_option maxHeartbeats 400000 in
-- Elaborating the two section-module equivalences requires the larger budget.
private def integralRestrictionSquare (X : Scheme.{u})
    (r : At l (LiftedQ.{u} l) X) :
    Mod.comap (integralToRational X l) ⋙ (integralEncoding X l r).functor ≅
      (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor ⋙
        pbcRestrict (scalarMap X l r) := by
  let H := adicLisseForget X
  let e := H.mapIso (integralComparison X l r)
  let b := H.mapIso r.sectionIso
  let a := H.map (sectionRingMap X (integralToRational X l))
  let ψ := H.map (scalarMap X l r)
  have h : e.inv ≫ a = ψ ≫ b.inv := by
    have h₀ : (integralComparison X l r).hom ≫ scalarMap X l r =
        sectionRingMap X (integralToRational X l) ≫ r.sectionIso.hom := by
      unfold integralComparison scalarMap
      exact (integralComparison_existsUnique X l r).exists.choose_spec
    have hh := congrArg (fun f ↦ (integralComparison X l r).inv ≫ f ≫
      r.sectionIso.inv) h₀
    have hh' : (integralComparison X l r).inv ≫
        sectionRingMap X (integralToRational X l) =
        scalarMap X l r ≫ r.sectionIso.inv := by
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
        Category.comp_id] using hh.symm
    exact (H.map_comp _ _).symm.trans ((congrArg H.map hh').trans (H.map_comp _ _))
  let c := ringModuleSquare X e b a ψ h
  unfold integralEncoding moduleEncoding
  exact Functor.isoWhiskerRight (sectionModuleComapIso X (integralToRational X l))
    (ringModuleEquivalenceOfIso X e.symm).functor ≪≫
      Functor.isoWhiskerLeft
        (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
          (ProEt.topology X) (Coefficient (LiftedQ.{u} l) X)).functor c

private theorem integralToQbar_factor' (X : Scheme.{u}) :
    integralToRational X l ≫ rationalToQbar X l = integralToQbar X l := by
  let F := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})) ⋙ upperStarFromPoint X
  change F.map _ ≫ F.map _ = F.map _
  rw [← F.map_comp]
  rfl

private def ordinaryRestrictionIso (X : Scheme.{u})
    (r : At l (LiftedQ.{u} l) X) :
    Mod.comap (integralToQbar X l) ⋙ (integralEncoding X l r).functor ≅
      ordinaryRestriction X l r :=
  Functor.isoWhiskerRight
    (Mod.comapCongr (integralToQbar_factor' l X).symm ≪≫
      Mod.comapComp (integralToRational X l) (rationalToQbar X l))
    (integralEncoding X l r).functor ≪≫
      Functor.isoWhiskerLeft (Mod.comap (rationalToQbar X l))
        (integralRestrictionSquare l X r)

private abbrev ordinaryExtension (X : Scheme.{u}) (r : At l (LiftedQ.{u} l) X) :=
  (integralEncoding X l r).inverse ⋙ Mod.extendScalars (integralToQbar X l)

private def ordinaryAdjunction (X : Scheme.{u}) (r : At l (LiftedQ.{u} l) X) :
    ordinaryExtension l X r ⊣ ordinaryRestriction X l r :=
  ((integralEncoding X l r).symm.toAdjunction.comp
    (Mod.extendRestrictAdjunction (integralToQbar X l))).ofNatIsoRight
      (ordinaryRestrictionIso l X r)

private def encodedPowerIso (X : Scheme.{u}) (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    (ordinaryExtension l X r).obj
        ((integralEncoding X l r).functor.obj (integralPower X l d)) ≅
      tateTwistNat X l d :=
  (Mod.extendScalars (integralToQbar X l)).mapIso
    ((integralEncoding X l r).unitIso.symm.app (integralPower X l d)) ≪≫
      ordinaryPowerIso l X d

private theorem equivalence_inverseUnit_transpose
    {A B : Type*} [Category A] [Category B] (E : A ≌ B)
    (M N : A) (f : M ⟶ N) :
    E.symm.toAdjunction.homEquiv (E.functor.obj M) N
        (E.unitIso.inv.app M ≫ f) = E.functor.map f := by
  change E.counitIso.inv.app (E.functor.obj M) ≫
    E.functor.map (E.unitIso.inv.app M ≫ f) = E.functor.map f
  rw [E.functor.map_comp, ← Category.assoc, E.counitIso_functor_comp]
  erw [Category.id_comp]

private theorem encodedPowerIso_transpose (X : Scheme.{u})
    (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    (ordinaryAdjunction l X r).homEquiv _ _ (encodedPowerIso l X r d).hom =
      encodedBalancedPower X l r d := by
  have h : (ordinaryAdjunction l X r).homEquiv _ _ (encodedPowerIso l X r d).hom =
      (integralEncoding X l r).functor.map (balancedPower X l d) ≫
        (ordinaryRestrictionIso l X r).hom.app (tateTwistNat X l d) := by
    dsimp only [ordinaryAdjunction]
    erw [Adjunction.homEquiv_ofNatIsoRight_apply]
    erw [Adjunction.comp_homEquiv]
    dsimp only [Equiv.trans_apply, encodedPowerIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Iso.app_inv]
    rw [Adjunction.homEquiv_naturality_left]
    erw [ordinaryPowerIso_transpose]
    erw [equivalence_inverseUnit_transpose]
  rw [h]
  apply (encodedBalancedPower_existsUnique X l r d).unique
  · intro V x
    unfold integralEncoding
    dsimp [ordinaryRestrictionIso, integralRestrictionSquare, ringModuleSquare,
      integralEncoding, moduleEncoding]
    unfold integralEncoding
    rfl
  · exact (encodedBalancedPower_existsUnique X l r d).exists.choose_spec

/-- The adjoint of the specified balanced tensor map is invertible before reconstruction.
Source: Stacks 03EK, 06YU, 0G7E and 07A4; Steps 5, 7 and 8 of the realization argument
(blueprint: lem-route-scalar-balanced-power-is-iso).

Proof: Rationalization of the integral coefficient ring is exact because the rational
coefficient module is the sequential colimit of multiplication by l on the regular
integral module, and filtered colimits of abelian sheaves are exact. The canonical
universe-lift isomorphism and exact extension from rational coefficients to the
finite-extension-valued closure make integral-to-closure scalar extension exact.
Its existing strong monoidal structure identifies extension of every integral tensor
power with the corresponding Tate twist. The unit and successor formulas of its
ordinary adjunction make the transposes a balanced power family, hence uniqueness
identifies them with balancedPower. The normalized integralComparison square gives
the restriction comparison through integralEncoding; its maps preserve underlying
sections, so the corresponding transpose is encodedBalancedPower. Localize this
exact ordinary adjunction on cochain complexes, and compute its Hom correspondence
on single complexes using the unit and the standard exact-functor comparisons.
Transport its right adjoint by restrictionComparison. Uniqueness of left adjoints
then compares its left adjoint with the recorded ambientRealization, with the unit
normalization intact. The composite isomorphism thus has transpose exactly
derivedBalancedPower, so the inverse Hom correspondence in the statement equals
its invertible hom. This also treats the zeroth power by the monoidal unit and
requires no local generator, constructibility, or derived-limit comparison. -/
theorem scalarBalancedPower_isIso (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] (T : Base k)
    (r : At l (LiftedQ.{u} l) T.scheme) (d : ℕ) :
    IsIso (((scalarAdjunction T.scheme l r).homEquiv
      ((DerivedCategory.singleFunctor _ 0).obj
        ((integralEncoding T.scheme l r).functor.obj (integralPower T.scheme l d)))
      (tateTwistDerived T.scheme l (d : ℤ))).symm
        (derivedBalancedPower T.scheme l r d)) := by
  let X := T.scheme
  let E := integralEncoding X l r
  let F := ordinaryExtension l X r
  let G := ordinaryRestriction X l r
  let : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let : PreservesFiniteLimits (Mod.extendScalars (integralToQbar X l)) :=
    integralClosure_exact l X
  let : F.Additive := inferInstance
  let : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits F := comp_preservesFiniteColimits _ _
  let a := ordinaryAdjunction l X r
  let aD := (exactDerivedAdjunction a).ofNatIsoRight (restrictionComparison X l r)
  let b := scalarAdjunction X l r
  let M := E.functor.obj (integralPower X l d)
  let N := tateTwistNat X l d
  let e : (ambientRealization X l r).obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj N :=
    (b.leftAdjointUniq aD).app _ ≪≫
      (F.mapDerivedCategorySingleFunctor 0).app M ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (encodedPowerIso l X r d)
  have he : b.homEquiv _ _ e.hom = derivedBalancedPower X l r d := by
    dsimp only [e, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    erw [Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, exactDerivedAdjunction_single,
      encodedPowerIso_transpose]
    exact Category.assoc _ _ _
  have hq : (b.homEquiv _ _).symm (derivedBalancedPower X l r d) = e.hom := by
    rw [← he]
    exact Equiv.symm_apply_apply _ _
  change IsIso ((b.homEquiv _ _).symm (derivedBalancedPower X l r d))
  rw [hq]
  exact e.isIso_hom

end AlgebraicGeometry.ProEtale.CondensedTateRealization
