/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Sheaf.Paper.FiniteLineTensorConditions
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Field.ULift
import all Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackDualFreeChart
import all Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteGlobalPresentationInternalHomColimit
import WeilConjectures.Algebra.Homology.HomComplexComponents
import all Sheaf.Algebra.Homology.KFlatResolutionGeneral
import all Sheaf.Algebra.Homology.RingedSiteBoundedEvaluationAssembly

/-! # Internal Hom from a finite local system over a finite field

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.7.13,
finite-coefficient local-system case; Stacks Project, Tag 0FNY, example-dual
(blueprint: lem-sfb-finite-field-lisse-internal-hom).

The two functors below spell out the two sides of the cohomology formula, including
all maps. The theorem asserts bounded constructibility in the original interval and
an isomorphism natural contravariantly in the local system and covariantly in the complex.
All derived categories are the ordinary, uncompleted localizations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
attribute [-instance] CategoryTheory.RingedSiteBoundedEvaluation.smallColimits
  CategoryTheory.RingedSiteBoundedEvaluation.hasTotal
  CategoryTheory.RingedSiteBoundedEvaluation.finiteBiproducts

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

private def uncurryTensorIso_ff
    (Q : Type*) [Category Q] [MonoidalCategory Q] :
    Functor.uncurry.obj (curriedTensor Q) ≅ tensor Q :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    change (_ ≫ _) ≫ 𝟙 _ = 𝟙 _ ≫ (_ ⊗ₘ _)
    rw [Category.comp_id, Category.id_comp, tensorHom_def]
    rfl)


private def tensorEvaluationLeftIso_ff
    {C : Type*} [Category C] [MonoidalCategory C]
    (D : Cᵒᵖ ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (τ : D.prod (𝟭 C) ⋙ tensor C ⟶ Functor.uncurry.obj H)
    (X : C) [∀ Y, IsIso (τ.app (op X, Y))] :
    tensorLeft (D.obj (op X)) ≅ H.obj (op X) := by
  refine NatIso.ofComponents (fun Y ↦ asIso (τ.app (op X, Y))) ?_
  intro Y Y' f
  have h := τ.naturality (Prod.mkHom (𝟙 (op X)) f)
  change (D.map (𝟙 (op X)) ⊗ₘ f) ≫ τ.app (op X, Y') =
    τ.app (op X, Y) ≫ ((H.map (𝟙 (op X))).app Y ≫ (H.obj (op X)).map f) at h
  rw [D.map_id, H.map_id] at h
  change (𝟙 _ ⊗ₘ f) ≫ τ.app (op X, Y') =
    τ.app (op X, Y) ≫ (𝟙 _ ≫ (H.obj (op X)).map f) at h
  rw [id_tensorHom, Category.id_comp] at h
  exact h


private def directEvaluationNat_ff
    {B : Type*} [Category B] {C : Type*} [Category C]
    [MonoidalCategory C] [BraidedCategory C]
    (D : B ⥤ C) (H : B ⥤ C ⥤ C)
    (E : ∀ b X, X ⊗ D.obj b ⟶ (H.obj b).obj X)
    (hl : ∀ {b b'} (f : b ⟶ b') X,
      X ◁ D.map f ≫ E b' X = E b X ≫ (H.map f).app X)
    (hr : ∀ b {X X'} (f : X ⟶ X'),
      f ▷ D.obj b ≫ E b X' = E b X ≫ (H.obj b).map f) :
    (D.prod (𝟭 C)) ⋙ tensor C ⟶ Functor.uncurry.obj H where
  app P := (β_ (D.obj P.1) P.2).hom ≫ E P.1 P.2
  naturality {P Q} f := by
    change (D.map f.1 ⊗ₘ f.2) ≫ ((β_ _ _).hom ≫ E Q.1 Q.2) =
      ((β_ _ _).hom ≫ E P.1 P.2) ≫ ((H.map f.1).app P.2 ≫ (H.obj Q.1).map f.2)
    rw [← Category.assoc, BraidedCategory.braiding_naturality, Category.assoc, tensorHom_def']
    simp only [Category.assoc]
    rw [hr]
    rw [← Category.assoc (P.2 ◁ D.map f.1) (E Q.1 P.2), hl]
    simp only [Category.assoc]

namespace PresheafOfModules

variable {C : Type (u + 1)} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u + 1}}
  (M P : PresheafOfModules.{u + 1} (R ⋙ forget₂ _ _))

private lemma app_unit_eq_smul_ff {U : C}
    (s : (restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj M)
    (W : (Over U)ᵒᵖ) (r : R.obj (op W.unop.left)) :
    s.app W r = r • (show M.obj (op W.unop.left) from
      M.map W.unop.hom.op (s.app (op (Over.mk (𝟙 U))) (1 : R.obj (op U)))) := by
  have h1 : s.app W (1 : R.obj (op W.unop.left)) =
      M.map W.unop.hom.op (s.app (op (Over.mk (𝟙 U))) (1 : R.obj (op U))) :=
    (congrArg (s.app W) (unit_map_one (R := R ⋙ forget₂ _ _) W.unop.hom.op).symm).trans
      (naturality_apply s
        (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 U)).op _)
  refine (congrArg (s.app W) (mul_one r).symm).trans ?_
  refine ((s.app W).hom.map_smul r (1 : R.obj (op W.unop.left))).trans ?_
  exact congrArg (fun y : M.obj (op W.unop.left) ↦ r • y) h1

private noncomputable def dualTensorHom_ff : homObj M (unit _) ⊗ P ⟶ homObj M P :=
  tensorHomCurry_kfg ((α_ M (homObj M (unit _)) P).inv ≫
    tensorHomUncurry_kfg (𝟙 _) ▷ P ≫ (λ_ P).hom)

/-- `Hom(M, R) ⊗ P ⟶ Hom(M, P)` sends `φ ⊗ p` to `m ↦ φ(m) • p`. -/
private lemma dualTensorHom_ff_app_tmul_app_apply {U : C} (φ : (homObj M (unit _)).obj (op U))
    (p : P.obj (op U)) (W : (Over U)ᵒᵖ) (m : M.obj (op W.unop.left)) :
    (((dualTensorHom_ff M P).app (op U) (φ ⊗ₜ p)).app W) m =
      (show R.obj (op W.unop.left) from (φ.app W) m) • P.map W.unop.hom.op p := by
  refine (?_ : _ = (show R.obj (op W.unop.left) from
    (φ.app (op (Over.mk (𝟙 W.unop.left ≫ W.unop.hom)))) m) • P.map W.unop.hom.op p).trans ?_
  · rfl
  · rw [restrictOver_hom_app_congr φ (Category.id_comp W.unop.hom) m]
    rfl

variable {M P} in
private lemma dualTensorHom_ff_app_bijective_of_free {U : C} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ((restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj M))
    (c : ι → ((restrictOver R U).obj M ⟶ (restrictOver R U).obj (unit _)))
    (hsc : ∀ i j, s j ≫ c i = if j = i then 𝟙 _ else 0)
    (htot : ∑ i, c i ≫ s i = 𝟙 _) :
    Function.Bijective ((dualTensorHom_ff M P).app (op U)) := by
  let T : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))
  let m : ι → M.obj (op U) := fun i ↦ (s i).app T (1 : R.obj (op U))
  -- Every section of `M` over `W ⟶ U` is a combination of the restrictions of the `m i`.
  have hspan (W : (Over U)ᵒᵖ) (x : M.obj (op W.unop.left)) :
      x = ∑ i, (show R.obj (op W.unop.left) from (c i).app W x) •
        (show M.obj (op W.unop.left) from M.map W.unop.hom.op (m i)) := by
    have h : ∑ i, (c i ≫ s i).app W x = x :=
      (sum_app_apply Finset.univ (fun i ↦ c i ≫ s i) W x).symm.trans
        (congrArg (fun f ↦ f.app W x) htot)
    exact h.symm.trans (Finset.sum_congr rfl fun i _ ↦ app_unit_eq_smul_ff M (s i) W _)
  have hcm (i j : ι) : (c i).app T (m j) = if j = i then (1 : R.obj (op U)) else 0 := by
    have h := congrArg (fun f ↦ f.app T (1 : R.obj (op U))) (hsc i j)
    refine h.trans ?_
    split_ifs <;> rfl
  -- A morphism out of `M|_U` is determined by its values on the `m i`.
  have hval {Q : PresheafOfModules.{u + 1} (R ⋙ forget₂ _ _)}
      (ψ : (restrictOver R U).obj M ⟶ (restrictOver R U).obj Q) (W : (Over U)ᵒᵖ)
      (x : M.obj (op W.unop.left)) :
      ψ.app W x = ∑ i, (show R.obj (op W.unop.left) from (c i).app W x) •
        (show Q.obj (op W.unop.left) from Q.map W.unop.hom.op (ψ.app T (m i))) := by
    refine (congrArg (ψ.app W) (hspan W x)).trans ?_
    refine (map_sum (ψ.app W).hom _ _).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    refine ((ψ.app W).hom.map_smul _ _).trans (congrArg (_ • ·) ?_)
    exact naturality_apply ψ
      (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 U)).op (m i)
  let c' : ι → (homObj M (unit _)).obj (op U) := c
  let a (φ : (homObj M (unit _)).obj (op U)) (i : ι) :
      (R ⋙ forget₂ CommRingCat RingCat).obj (op U) :=
    (show R.obj (op U) from φ.app T (m i))
  -- Every dual element is a combination of the `c i`.
  have hdual (φ : (homObj M (unit _)).obj (op U)) : φ = ∑ i, a φ i • c' i := by
    refine hom_ext (M₁ := (restrictOver R U).obj M) (M₂ := (restrictOver R U).obj (unit _))
      fun W ↦ ?_
    ext y
    refine (hval φ W y).trans ?_
    refine Eq.trans ?_ (sum_app_apply _ _ W y).symm
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    refine Eq.trans ?_ (restrictOver_smul_app_apply _ (c i) W y).symm
    change (show R.obj (op W.unop.left) from (c i).app W y) *
        (show R.obj (op W.unop.left) from R.map W.unop.hom.op (φ.app T (m i))) =
      R.map W.unop.hom.op (φ.app T (m i)) * (show R.obj (op W.unop.left) from (c i).app W y)
    exact mul_comm _ _
  -- Every element of `Hom(M, R) ⊗ P` over `U` is `∑ i, c i ⊗ pᵢ`.
  have key (t : ((homObj M (unit _)) ⊗ P).obj (op U)) :
      ∃ p : ι → P.obj (op U), t = ∑ i, c' i ⊗ₜ p i := by
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul φ q =>
      refine ⟨fun i ↦ a φ i • q, ?_⟩
      conv_lhs => rw [hdual φ]
      rw [TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun i _ ↦ TensorProduct.smul_tmul _ _ _
    | add t t' ht ht' =>
      obtain ⟨p, rfl⟩ := ht
      obtain ⟨p', rfl⟩ := ht'
      exact ⟨p + p', by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]⟩
  have hsingle (i j : ι) (p : P.obj (op U)) :
      ((dualTensorHom_ff M P).app (op U) (c' i ⊗ₜ p)).app T (m j) = if j = i then p else 0 := by
    rw [dualTensorHom_ff_app_tmul_app_apply, hcm]
    split_ifs
    · exact (one_smul _ _).trans (by
        change P.map (𝟙 (op U)) p = p
        rw [map_id]
        rfl)
    · exact zero_smul _ _
  -- The image of `∑ i, c i ⊗ pᵢ` sends `m j` to `p j`.
  have himage (p : ι → P.obj (op U)) (j : ι) :
      ((dualTensorHom_ff M P).app (op U) (∑ i, c' i ⊗ₜ p i)).app T (m j) = p j := by
    rw [map_sum, sum_app_apply]
    simp only [hsingle]
    simp
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨p, rfl⟩ := key t
    have hp (j : ι) : p j = 0 := by
      rw [← himage p j, ht]
      rfl
    simp [hp]
  · intro ψ
    refine ⟨∑ i, c' i ⊗ₜ ψ.app T (m i), ?_⟩
    refine hom_ext (M₁ := (restrictOver R U).obj M) (M₂ := (restrictOver R U).obj P)
      fun W ↦ ?_
    ext x
    rw [map_sum, sum_app_apply, hval ψ W x]
    exact Finset.sum_congr rfl fun i _ ↦ dualTensorHom_ff_app_tmul_app_apply M P _ _ W x


variable {M P} in
private lemma dualTensorHom_ff_app_bijective_of_hom {U : C} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ((restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj M))
    (c : ι → ((restrictOver R U).obj M ⟶ (restrictOver R U).obj (unit _)))
    (hsc : ∀ i j, s j ≫ c i = if j = i then 𝟙 _ else 0)
    (htot : ∑ i, c i ≫ s i = 𝟙 _) {V : C} (g : V ⟶ U) :
    Function.Bijective ((dualTensorHom_ff M P).app (op V)) := by
  refine dualTensorHom_ff_app_bijective_of_free (fun i ↦ restrictOverMap g (s i))
    (fun i ↦ restrictOverMap g (c i)) (fun i j ↦ ?_) ?_
  · change restrictOverMap g (s j ≫ c i) = _
    rw [hsc]
    split_ifs
    · exact restrictOverMap_id (R := R) (M := unit _) (N := unit _) (𝟙 _)
    · rfl
  · change ∑ i, restrictOverMap g (c i ≫ s i) = _
    let F : (((restrictOver R U).obj M ⟶ (restrictOver R U).obj M) →+
        ((restrictOver R V).obj M ⟶ (restrictOver R V).obj M)) :=
      { toFun := restrictOverMap g, map_zero' := rfl, map_add' _ _ := rfl }
    exact (map_sum F _ _).symm.trans (by rw [htot]; rfl)

end PresheafOfModules

namespace SheafOfModules



variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u + 1})]
  {R : Sheaf J CommRingCat.{u + 1}}

set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat RingCat.{u + 1})).obj R

section

variable {U : C}
/-- A morphism `M|_U ⟶ N|_U` of sheaves of modules over `Over U`, as a morphism between the
restrictions to `Over U` of the underlying presheaves of modules. -/
private noncomputable def toRestrictOverHom_ff {M N : SheafOfModules.{u + 1} 𝓡}
    (f : M.over U ⟶ N.over U) :
    (PresheafOfModules.restrictOver R.obj U).obj M.val ⟶
      (PresheafOfModules.restrictOver R.obj U).obj N.val :=
  (chart_overValIso.{u + 1, u, u + 1} M U).inv ≫ f.val ≫
    (chart_overValIso.{u + 1, u, u + 1} N U).hom

private lemma toRestrictOverHom_ff_id (M : SheafOfModules.{u + 1} 𝓡) :
    toRestrictOverHom_ff (𝟙 (M.over U)) = 𝟙 _ := by
  simp only [toRestrictOverHom_ff, id_val, Category.id_comp, Iso.inv_hom_id]

private lemma toRestrictOverHom_ff_zero (M N : SheafOfModules.{u + 1} 𝓡) :
    toRestrictOverHom_ff (0 : M.over U ⟶ N.over U) = 0 := by
  change (chart_overValIso.{u + 1, u, u + 1} M U).inv ≫ 0 ≫
    (chart_overValIso.{u + 1, u, u + 1} N U).hom = 0
  rw [zero_comp, comp_zero]

private lemma toRestrictOverHom_ff_add {M N : SheafOfModules.{u + 1} 𝓡}
    (f g : M.over U ⟶ N.over U) :
    toRestrictOverHom_ff (f + g) = toRestrictOverHom_ff f + toRestrictOverHom_ff g := by
  simp only [toRestrictOverHom_ff, add_val, Preadditive.add_comp, Preadditive.comp_add]

private lemma toRestrictOverHom_ff_sum {M N : SheafOfModules.{u + 1} 𝓡} {ι : Type*} (t : Finset ι)
    (f : ι → (M.over U ⟶ N.over U)) :
    toRestrictOverHom_ff (∑ i ∈ t, f i) = ∑ i ∈ t, toRestrictOverHom_ff (f i) :=
  map_sum (AddMonoidHom.mk' toRestrictOverHom_ff toRestrictOverHom_ff_add :
      (M.over U ⟶ N.over U) →+ ((PresheafOfModules.restrictOver R.obj U).obj M.val ⟶
        (PresheafOfModules.restrictOver R.obj U).obj N.val)) f t

end

variable {U : C} in
/-- If `M` is free of finite rank on `U`, then `Hom(M, R) ⊗ N ⟶ Hom(M, N)` is bijective on
sections over every `V ⟶ U`. -/
private lemma dualTensorHom_ff_app_bijective_of_iso_free
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u + 1}] (M N : SheafOfModules.{u + 1} 𝓡)
    {I : Type (u + 1)} [Finite I] (e : free I ≅ M.over U) {V : C} (g : V ⟶ U) :
    Function.Bijective
      ((PresheafOfModules.dualTensorHom_ff (R := R.obj) M.val N.val).app (op V)) := by
  classical
  let := Fintype.ofFinite I
  let S (j : I) : (unit 𝓡).over U ⟶ M.over U := Sigma.ι (fun _ ↦ unit _) j ≫ e.hom
  let Cc (j : I) : M.over U ⟶ (unit 𝓡).over U :=
    e.inv ≫ Sigma.desc (fun k ↦ if k = j then 𝟙 (unit _) else 0)
  have hsc (i j : I) : S j ≫ Cc i = if j = i then 𝟙 _ else 0 := by
    dsimp only [S, Cc]
    erw [Category.assoc, Iso.hom_inv_id_assoc, Sigma.ι_desc]
    rfl
  have hsum : ∑ i, Sigma.desc (fun k ↦ if k = i then 𝟙 (unit _) else 0) ≫
      Sigma.ι (fun _ : I ↦ unit ((𝓡).over U)) i = 𝟙 (free I) := by
    refine Sigma.hom_ext _ _ fun k ↦ ?_
    rw [Preadditive.comp_sum, Finset.sum_eq_single k (fun b _ hb ↦ by simp [Ne.symm hb])
      (by simp)]
    simp only [Sigma.ι_desc_assoc]
    exact (Category.comp_id _).symm
  have htot : ∑ i, Cc i ≫ S i = 𝟙 _ := by
    calc ∑ i, Cc i ≫ S i = e.inv ≫ (∑ i, Sigma.desc (fun k ↦ if k = i then 𝟙 (unit _) else 0) ≫
          Sigma.ι (fun _ : I ↦ unit ((𝓡).over U)) i) ≫ e.hom := by
          dsimp only [Cc, S]
          erw [Preadditive.sum_comp, Preadditive.comp_sum]
          exact Finset.sum_congr rfl (fun i _ ↦ by
            simp only [Category.assoc]
            rfl)
      _ = 𝟙 _ := by erw [hsum, Category.id_comp, Iso.inv_hom_id]
  refine PresheafOfModules.dualTensorHom_ff_app_bijective_of_hom (R := R.obj) (P := N.val) (U := U)
    (fun j ↦ toRestrictOverHom_ff (S j)) (fun j ↦ toRestrictOverHom_ff (Cc j)) (fun i j ↦ ?_) ?_ g
  · refine (congrArg toRestrictOverHom_ff (hsc i j)).trans ?_
    split_ifs
    · exact toRestrictOverHom_ff_id _
    · exact toRestrictOverHom_ff_zero _ _
  · exact (toRestrictOverHom_ff_sum Finset.univ (fun i ↦ Cc i ≫ S i)).symm.trans
      ((congrArg toRestrictOverHom_ff htot).trans (toRestrictOverHom_ff_id M))





section
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

open CategoryTheory.RingedSiteBoundedEvaluation

private def dualFunctor_ff : (SheafOfModules.{u + 1} 𝓡)ᵒᵖ ⥤ SheafOfModules.{u + 1} 𝓡 :=
  (homFunctor.{u + 1, u, u + 1, u + 1} R).flip.obj (unit _)


omit [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
private lemma evaluationPresheaf_eq_ff (M N : SheafOfModules.{u + 1} 𝓡) :
    evaluationPresheaf.{u + 1, u, u + 1}
        R M N =
      (β_ N.val (PresheafOfModules.homObj M.val (PresheafOfModules.unit _))).hom ≫
        PresheafOfModules.dualTensorHom_ff (R := R.obj) M.val N.val := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro y φ
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (((evaluationPresheaf.{u + 1, u, u + 1}
     R M N).app U (y ⊗ₜ φ)).app W).hom x =
      (((PresheafOfModules.dualTensorHom_ff (R := R.obj) M.val N.val).app U
        (φ ⊗ₜ y)).app W).hom x
  simp only [evaluationPresheaf]
  erw [TensorProduct.lift.tmul]
  rw [evaluationBilinear_apply]
  exact (PresheafOfModules.dualTensorHom_ff_app_tmul_app_apply M.val N.val φ y W x).symm

private theorem evaluationNat_exists_ff
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    ∃ τ : ((dualFunctor_ff (R := R)).prod (𝟭 _)) ⋙ tensor (SheafOfModules.{u + 1} 𝓡) ⟶
        Functor.uncurry.obj (homFunctor.{u + 1, u, u + 1, u + 1} R),
      ∀ M N : SheafOfModules.{u + 1} 𝓡, M.IsFiniteLocallyFree →
        IsIso (τ.app (op M, N)) := by
  let τ := directEvaluationNat_ff (dualFunctor_ff (R := R))
    (homFunctor.{u + 1, u, u + 1, u + 1} R)
    (fun L N ↦ moduleEvaluation.{u + 1, u, u + 1} R L.unop N)
    (fun {L L'} f N ↦ moduleEvaluation_natural_left.{u + 1, u, u + 1}
       R f.unop N)
    (fun L {_ _} f ↦ moduleEvaluation_natural_right.{u + 1, u, u + 1} R L.unop f)
  refine ⟨τ, ?_⟩
  intro M N hM
  let : M.IsFiniteLocallyFree := hM
  obtain ⟨q, hq, hf⟩ := IsFiniteLocallyFree.exists_localGeneratorsData (M := M)
  have hb (V : C) (i : q.I) (g : V ⟶ q.X i) :
      Function.Bijective
        ((PresheafOfModules.dualTensorHom_ff (R := R.obj) M.val N.val).app (op V)) := by
    have := (hf.isFiniteType i).finite
    have := hq.isIso i
    exact dualTensorHom_ff_app_bijective_of_iso_free M N (asIso (q.generators i).π) g
  have hW : J.W.inverseImage (PresheafOfModules.toPresheaf (𝓡).obj)
      (PresheafOfModules.dualTensorHom_ff (R := R.obj) M.val N.val) :=
    (GrothendieckTopology.W_iff_isLocallyBijective _ _).2
      ⟨Presheaf.isLocallyInjective_of_coversTop q.coversTop _ fun V i g ↦ (hb V i g).1,
        Presheaf.isLocallySurjective_of_coversTop q.coversTop _ fun V i g ↦ (hb V i g).2⟩
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (𝟙 (𝓡).obj)] at hW
  let A := PresheafOfModules.sheafification (𝟙 (𝓡).obj)
  have : IsIso (A.map
    (PresheafOfModules.dualTensorHom_ff (R := R.obj) M.val N.val)) := hW
  have : IsIso (A.map
      (evaluationPresheaf.{u + 1, u, u + 1} R M N)) := by
    rw [evaluationPresheaf_eq_ff (R := R), A.map_comp]
    infer_instance
  have : IsIso (moduleEvaluation.{u + 1, u, u + 1} R M N) := by
    unfold moduleEvaluation
      tensorLift
    rw [Adjunction.homEquiv_counit]
    infer_instance
  change IsIso ((β_ _ _).hom ≫
    moduleEvaluation.{u + 1, u, u + 1} R M N)
  infer_instance

private theorem finiteFreeEvaluationIso_ff
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (M : SheafOfModules.{u + 1} 𝓡) [M.IsFiniteLocallyFree] :
    Nonempty (tensorLeft (homObj M (unit _)) ≅
      (homFunctor.{u + 1, u, u + 1, u + 1} R).obj (op M)) := by
  obtain ⟨τ, hτ⟩ := evaluationNat_exists_ff (R := R)
  let : ∀ N, IsIso (τ.app (op M, N)) := fun N ↦ hτ M N inferInstance
  exact ⟨tensorEvaluationLeftIso_ff (dualFunctor_ff (R := R))
    (homFunctor.{u + 1, u, u + 1, u + 1} R) τ M⟩

private theorem finiteFreeHomColimits_ff
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (M : SheafOfModules.{u + 1} 𝓡) [M.IsFiniteLocallyFree] :
    PreservesColimitsOfSize.{u + 1, u + 1}
      ((homFunctor.{u + 1, u, u + 1, u + 1} R).obj (op M)) := by
  have : PreservesColimitsOfSize.{u + 1, u + 1} (tensorLeft (homObj M (unit _))) :=
    (tensorHomAdjunction_kfg R (homObj M (unit _))).leftAdjoint_preservesColimits
  obtain ⟨e⟩ := finiteFreeEvaluationIso_ff M
  exact preservesColimits_of_natIso e

end

end SheafOfModules

private def restrictTensorEvaluationIso_ff
    {B C : Type*} [Category B] [Category C] [MonoidalCategory C]
    (i : B ⥤ Cᵒᵖ) (D : Cᵒᵖ ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (τ : D.prod (𝟭 C) ⋙ tensor C ⟶ Functor.uncurry.obj H)
    (hτ : ∀ (b : B) (N : C), IsIso (τ.app (i.obj b, N))) :
    ((i ⋙ D).prod (𝟭 C)) ⋙ Functor.uncurry.obj (curriedTensor C) ≅
      (i.prod (𝟭 C)) ⋙ Functor.uncurry.obj H := by
  let τ' := Functor.whiskerLeft (i.prod (𝟭 C)) τ
  have : IsIso τ' := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro P
    exact hτ P.1 P.2
  exact Functor.isoWhiskerLeft ((i ⋙ D).prod (𝟭 C)) (uncurryTensorIso_ff C) ≪≫ asIso τ'


namespace AlgebraicGeometry.Scheme

attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The existing locally bijective criterion in the fixed finite-coefficient universe.
This specializes the general coefficient-universe instance explicitly, so that an
unrelated completed-coefficient instance cannot leave a free universe metavariable.
Source: Stacks Project, Modules on Sites, Section 03DA
(blueprint: lem-sfb-finite-field-lisse-internal-hom). -/
instance finiteFieldInternalHom_locallyBijective (S : Scheme.{u}) :
    (ProEt.topology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}


/-- The bifunctor `(L,N) ↦ H^r RHom(L[0],N)` on the ordinary constant-ring module
category. The first variable is contravariant. Source: the K-injective construction
in Stacks, Cohomology on Sites, Section 08J7
(blueprint: lem-sfb-finite-field-lisse-internal-hom). -/
def finiteFieldInternalHomCohomology (S : Scheme.{u}) (A : Type u) [Field A] (r : ℤ) :
    (proEtaleRingModules S (proEtaleConstantRing S A))ᵒᵖ ×
      DerivedCategory.{u + 2} (proEtaleRingModules S (proEtaleConstantRing S A)) ⥤
        proEtaleRingModules S (proEtaleConstantRing S A) :=
  ((DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2}
      (proEtaleRingModules S (proEtaleConstantRing S A)) 0).op.prod
    (𝟭 (DerivedCategory.{u + 2} (proEtaleRingModules S (proEtaleConstantRing S A))))) ⋙
    derivedInternalHomOfUniverses.{u + 1, u, u + 1, u + 2}
      (ProEt.topology S) (proEtaleConstantRing S A) ⋙
    DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2}
      (proEtaleRingModules S (proEtaleConstantRing S A)) r

/-- The bifunctor `(L,N) ↦ Hom(L,A_S) ⊗ H^r(N)`, using the existing sheaf Hom and
sheafification tensor product; its first variable acts by precomposition.
Source: Stacks Project, Tag 0FNY, example-dual, finite-free evaluation formula
(blueprint: lem-sfb-finite-field-lisse-internal-hom). -/
def finiteFieldDualTensorCohomology (S : Scheme.{u}) (A : Type u) [Field A] (r : ℤ) :
    (proEtaleRingModules S (proEtaleConstantRing S A))ᵒᵖ ×
      DerivedCategory.{u + 2} (proEtaleRingModules S (proEtaleConstantRing S A)) ⥤
        proEtaleRingModules S (proEtaleConstantRing S A) :=
  (((SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1}
      (proEtaleConstantRing S A)).flip.obj
        (SheafOfModules.unit ((sheafCompose (ProEt.topology S)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing S A)))).prod
    (DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2}
      (proEtaleRingModules S (proEtaleConstantRing S A)) r)) ⋙
      Functor.uncurry.obj
        (curriedTensor (proEtaleRingModules S (proEtaleConstantRing S A)))

private def modelPresheafFunctor (S : Scheme.{u}) (A : Type u) [CommRing A]
    (U : S.ProEt) : ModuleCat.{u + 1} (ULift.{u + 1} A) ⥤
      _root_.PresheafOfModules.{u + 1}
        ((Functor.const (Over U)ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) where
  obj M := proEtaleConstantModulePresheafOfUniverses (Over U) A M
  map f := { app := fun _ ↦ f }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private instance (S : Scheme.{u}) (A : Type u) [CommRing A] (U : S.ProEt) :
    (modelPresheafFunctor S A U).Additive where
  map_add {X Y f g} := by ext; rfl

private def modelSheafFunctor (S : Scheme.{u}) (A : Type u) [CommRing A]
    (U : S.ProEt) : ModuleCat.{u + 1} (ULift.{u + 1} A) ⥤
      SheafOfModules.{u + 1}
        (((sheafCompose (ProEt.topology S)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing S A)).over U) :=
  let : EssentiallySmall.{u + 1} (Over U) := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify ((ProEt.topology S).over U) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite _ _
  let : ((ProEt.topology S).over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  haveI := (proEtaleConstantRingUnit_over_locallyBijectiveOfUniverses S A U).1
  haveI := (proEtaleConstantRingUnit_over_locallyBijectiveOfUniverses S A U).2
  modelPresheafFunctor S A U ⋙ _root_.PresheafOfModules.sheafification.{u + 1}
    (Functor.whiskerLeft (Over.forget U).op
      (Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology S)
        ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})))

private instance sheafificationAdditive_ff
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R₀ : Cᵒᵖ ⥤ RingCat.{u + 1}} {R : Sheaf J RingCat.{u + 1}} (α : R₀ ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}] :
    (_root_.PresheafOfModules.sheafification.{u + 1} α).Additive := by
  let L := _root_.PresheafOfModules.sheafification.{u + 1} α
  have : PreservesBinaryBiproducts L :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts L
  exact Functor.additive_of_preservesBinaryBiproducts L

private instance (S : Scheme.{u}) (A : Type u) [CommRing A] (U : S.ProEt) :
    (modelSheafFunctor S A U).Additive := by
  dsimp only [modelSheafFunctor]
  infer_instance

private theorem finiteModelFree (S : Scheme.{u}) (A : Type u) [Field A]
    (U : S.ProEt) (M : ModuleCat.{u + 1} (ULift.{u + 1} A))
    [Module.Finite (ULift.{u + 1} A) M] :
    ∃ (κ : Type (u + 1)) (_ : Finite κ),
      Nonempty (proEtaleConstantModuleSheafOverOfUniverses S A U M ≅
        SheafOfModules.free κ) := by
  classical
  let B := ULift.{u + 1} A
  let κ := Module.Free.ChooseBasisIndex B M
  let b := Module.Free.chooseBasis B M
  let F := modelSheafFunctor S A U
  let R := ((sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing S A)).over U
  let : HasFiniteBiproducts (SheafOfModules.{u + 1} R) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let e₁ : M ≅ ModuleCat.of B (κ → B) := b.equivFun.toModuleIso
  let e₂ : (⨁ fun _ : κ ↦ ModuleCat.of B B) ≅ ModuleCat.of B (κ → B) :=
    (biproduct.isLimit _).conePointUniqueUpToIso
      (ModuleCat.HasLimit.productLimitCone.{u + 1, 0, u + 1} _).isLimit
  let e : M ≅ ⨁ fun _ : κ ↦ ModuleCat.of B B := e₁ ≪≫ e₂.symm
  let eunit : F.obj (ModuleCat.of B B) ≅ SheafOfModules.unit R := by
    exact (WeilConjectures.constant_unit_over S A U).some.symm
  refine ⟨κ, inferInstance, ⟨?_⟩⟩
  change F.obj M ≅ SheafOfModules.free κ
  exact F.mapIso e ≪≫ F.mapBiproduct (fun _ : κ ↦ ModuleCat.of B B) ≪≫
    biproduct.mapIso (fun _ ↦ eunit) ≪≫
      biproduct.isoCoproduct (fun _ : κ ↦ SheafOfModules.unit R)

private theorem finiteModelsLocallyFree (S : Scheme.{u}) (A : Type u) [Field A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A))
    (hL : IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
      (fun M ↦ Module.Finite (ULift.{u + 1} A) M) L) : L.IsFiniteLocallyFree := by
  classical
  obtain ⟨I, U, f, hc, he⟩ := hL
  have hU : (ProEt.topology S).CoversTop U := by
    let hT : IsTerminal (ProEt.mk (𝟙 S)) := ProEt.isTerminalMkId S
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ hT]
    rw [← Sieve.ofArrows_eq_ofObjects hT U f]
    exact Precoverage.generate_mem_toGrothendieck hc
  have hfree (i : I) : ∃ (κ : Type (u + 1)) (_ : Finite κ),
      Nonempty (L.over (U i) ≅ SheafOfModules.free κ) := by
    obtain ⟨M, hM, ⟨e⟩⟩ := he i
    let := hM
    obtain ⟨κ, hκ, ⟨eM⟩⟩ := finiteModelFree S A (U i) M
    exact ⟨κ, hκ, ⟨e ≪≫ eM⟩⟩
  choose κ hκ eκ using hfree
  let := hκ
  exact SheafOfModules.isFiniteLocallyFree_of_exists_over_iso_free (M := L) U hU κ eκ

private theorem finiteLocallyFreeHomColimits (S : Scheme.{u}) (A : Type u) [Field A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A)) [L.IsFiniteLocallyFree] :
    PreservesColimitsOfSize.{u + 1, u + 1}
      ((SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1}
        (proEtaleConstantRing S A)).obj (op L)) := by
  exact SheafOfModules.finiteFreeHomColimits_ff (R := proEtaleConstantRing S A) L

private theorem finiteLocallyFreeHomLimits (S : Scheme.{u}) (A : Type u) [Field A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A)) :
    PreservesFiniteLimits
      ((SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1}
        (proEtaleConstantRing S A)).obj (op L)) := by
  let F := (SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1}
        (proEtaleConstantRing S A)).obj (op L)
  have : PreservesLimitsOfSize.{0, 0} F :=
    (SheafOfModules.tensorHomAdjunction_kfg
      (proEtaleConstantRing S A) L).rightAdjoint_preservesLimits
  infer_instance


private theorem dualFiniteModels (S : Scheme.{u}) (A : Type u) [Field A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A))
    (hL : IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
      (fun M ↦ Module.Finite (ULift.{u + 1} A) M) L) :
    IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
      (fun M ↦ Module.Finite (ULift.{u + 1} A) M)
      (SheafOfModules.homObj (R := proEtaleConstantRing S A) L (SheafOfModules.unit _)) := by
  classical
  obtain ⟨I, U, f, hc, he⟩ := hL
  refine ⟨I, U, f, hc, fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := he i
  let := hM
  obtain ⟨κ, hκ, ⟨eM⟩⟩ := finiteModelFree S A (U i) M
  let := Fintype.ofFinite κ
  let R := proEtaleConstantRing S A
  let RU := R.over (U i)
  let R₀ := ((sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over (U i)
  let : HasFiniteBiproducts (SheafOfModules.{u + 1} R₀) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  refine ⟨M, hM, ⟨?_⟩⟩
  exact SheafOfModules.chart_overHomIso.{u + 1, u, u + 1} L (SheafOfModules.unit _) (U i) ≪≫
    ((SheafOfModules.homFunctor RU).flip.obj (SheafOfModules.unit R₀)).mapIso
      (e ≪≫ eM).symm.op ≪≫
    SheafOfModules.SiteFinitePresentation.free_iso RU (SheafOfModules.unit R₀) κ ≪≫
    biproduct.isoCoproduct (fun _ : κ ↦ SheafOfModules.unit R₀) ≪≫ eM.symm

private theorem fixedFiniteModels (S : Scheme.{u}) (A : Type u) [Field A] [Finite A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A))
    (hL : IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
      (fun M ↦ Module.Finite (ULift.{u + 1} A) M) L) :
    ProEtale.IsFiniteLocallyConstant (ULift.{u + 1} A)
      ((proEtaleModuleRestriction S A).obj L) := by
  classical
  obtain ⟨I, U, f, hf, he⟩ := hL
  let B := ULift.{u + 1} A
  let F := (proEtaleModuleRestriction S A).obj L
  let R := (sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing S A)
  have hg : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
      proetalePrecoverage S := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hf
    change Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage S at hf
    have hw (i : I) : (f i).left = (U i).hom := by
      have hw := MorphismProperty.Over.w (f i)
      change (f i).left ≫ 𝟙 S = (U i).hom at hw
      exact (Category.comp_id _).symm.trans hw
    simpa only [hw] using hf
  refine ⟨I, fun i ↦ (U i).left, fun i ↦ (U i).hom, hg, fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := he i
  let := hM
  let a := Functor.whiskerLeft (Over.forget (U i)).op (proEtaleModuleScalarUnit S A)
  have ha := proEtaleConstantRingUnit_over_locallyBijective S A (U i)
  have hai : Presheaf.IsLocallyInjective ((ProEt.topology S).over (U i)) a := by
    simpa [a, proEtaleModuleScalarUnit, proEtaleConstantRing] using ha.1
  have has : Presheaf.IsLocallySurjective ((ProEt.topology S).over (U i)) a := by
    simpa [a, proEtaleModuleScalarUnit, proEtaleConstantRing] using ha.2
  let E := ConstantScalarComparison.restriction ((ProEt.topology S).over (U i))
    B (R.over (U i)) a
  have := ConstantScalarComparison.constantComparisonHom_isIso
    ((ProEt.topology S).over (U i)) B (R.over (U i)) a M
  let e : F.over (U i) ≅ (constantSheaf ((ProEt.topology S).over (U i))
      (ModuleCat.{u + 1} B)).obj M :=
    E.mapIso eM ≪≫
      (asIso (ConstantScalarComparison.constantComparisonHom
        ((ProEt.topology S).over (U i)) B (R.over (U i)) a M)).symm
  have : (ProEt.sliceEquiv S (U i)).inverse.IsDenseSubsite
      (ProEt.topology (U i).left) ((ProEt.topology S).over (U i)) :=
    ProEt.sliceDense S (U i)
  let D := (ProEt.sliceEquiv S (U i)).sheafCongr
    ((ProEt.topology S).over (U i)) (ProEt.topology (U i).left) (ModuleCat.{u + 1} B)
  let r : D.functor.obj (F.over (U i)) ≅
      (ProEtale.localizationRestriction (ModuleCat.{u + 1} B) (U i).hom (U i).prop).obj F :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  let c := ((ProEt.sliceEquiv S (U i)).constantSheafSheafCongrIso
    ((ProEt.topology S).over (U i)) (ProEt.topology (U i).left)
    (ModuleCat.{u + 1} B) (Over.mkIdTerminal (X := U i))).app M
  have : Finite M := Finite.of_equiv
    (Module.Free.ChooseBasisIndex B M → B) (Module.Free.chooseBasis B M).equivFun.toEquiv.symm
  exact ⟨M, inferInstance, ⟨
    (ProEtale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} B) (U i).hom (U i).prop).app F ≪≫
    r.symm ≪≫ D.functor.mapIso e ≪≫ c⟩⟩

private theorem finiteModelsTensorConstructible (S : Scheme.{u}) (A : Type u)
    [Field A] [Finite A]
    (L M : proEtaleRingModules S (proEtaleConstantRing S A))
    (hL : IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
      (fun M ↦ Module.Finite (ULift.{u + 1} A) M) L)
    (hM : IsConstructibleProEtaleModuleSheaf S A M) :
    IsConstructibleProEtaleModuleSheaf S A (L ⊗ M) := by
  let R := proEtaleConstantRing S A
  let E := sfIntrinsicModuleEquivalence S A
  let C := proEtaleModuleRestriction S A
  let FM := E.inverse.obj M
  let FL := E.inverse.obj L
  let eM : FM ≅ C.obj M := WeilConjectures.realization_restriction_iso S A FM ≪≫
    C.mapIso (E.counitIso.app M)
  let eL : FL ≅ C.obj L := WeilConjectures.realization_restriction_iso S A FL ≪≫
    C.mapIso (E.counitIso.app L)
  have hFM : ProEtale.IsConstructible (ULift.{u + 1} A) FM :=
    ProEtale.isConstructible_of_iso eM.symm
      ((proEtaleModuleRestriction_constructible_iff S A M).mp hM)
  have hFL : ProEtale.IsConstructible (ULift.{u + 1} A) FL := by
    refine ProEtale.isConstructible_of_iso eL.symm ⟨Stratification.trivial S, fun _ ↦ ?_⟩
    exact ProEtale.isFiniteLocallyConstant_of_iso
      ((ProEtale.upperStarId _ S).app _).symm (fixedFiniteModels S A L hL)
  have ht := WeilConjectures.fixed_constructible_tensor S A FL FM hFL hFM
  obtain ⟨q⟩ := AlgebraicGeometry.proEtale_intrinsic_tensorRight_comparison S A FM
  let e : L ⊗ M ≅ E.functor.obj (FL ⊗ FM) :=
    tensorIso (E.counitIso.app L).symm (E.counitIso.app M).symm ≪≫
      ((SheafOfModules.siteSheafTensorRightIso R (E.functor.obj FM)).app
        (E.functor.obj FL)).symm ≪≫ q.app FL
  apply (proEtaleModuleRestriction_constructible_iff S A _).mpr
  exact ProEtale.isConstructible_of_iso (C.mapIso e).symm
    (ProEtale.isConstructible_of_iso (WeilConjectures.realization_restriction_iso
      S A (FL ⊗ FM)) ht)



universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

private def mapComplexBifunctor_ff
    {B : Type u₁} [Category.{v₁} B]
    {C : Type u₂} [Category.{v₂} C] [Preadditive C]
    {D : Type u₃} [Category.{v₃} D] [Preadditive D]
    (F : B ⥤ C ⥤ D) [∀ b, (F.obj b).PreservesZeroMorphisms] :
    B ⥤ CochainComplex C ℤ ⥤ CochainComplex D ℤ where
  obj b := (F.obj b).mapHomologicalComplex (.up ℤ)
  map f := NatTrans.mapHomologicalComplex (F.map f) (.up ℤ)
  map_id b := by rw [F.map_id, NatTrans.mapHomologicalComplex_id]
  map_comp f g := by rw [F.map_comp, NatTrans.mapHomologicalComplex_comp]


private def HomComplexProjection_ff
    (C : Type u₂) [Category.{v₂} C] [Preadditive C]
    (F : Cᵒᵖ ⥤ C ⥤ C)
    (G : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ) :=
  ∀ (L M : CochainComplex C ℤ) (n p q : ℤ) (_h : p + n = q),
    (((G.obj (op L)).obj M).X n ⟶ (F.obj (op (L.X p))).obj (M.X q))

private def HomComplexLimit_ff
    (C : Type u₂) [Category.{v₂} C] [Preadditive C]
    (F : Cᵒᵖ ⥤ C ⥤ C)
    (G : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (π : HomComplexProjection_ff C F G) :=
  ∀ L M n, IsLimit (Fan.mk (((G.obj (op L)).obj M).X n)
    (fun p ↦ π L M n p (p + n) rfl))

private def HomComplexDifferential_ff
    (C : Type u₂) [Category.{v₂} C] [Preadditive C]
    (F : Cᵒᵖ ⥤ C ⥤ C)
    (G : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (π : HomComplexProjection_ff C F G) :=
  ∀ L M n m p q q' p' (_hnm : n + 1 = m) (hpq : p + m = q)
      (hq' : p + n = q') (hp' : p' + n = q),
    ((G.obj (op L)).obj M).d n m ≫ π L M m p q hpq =
      π L M n p q' hq' ≫ (F.obj (op (L.X p))).map (M.d q' q) -
        n.negOnePow • (π L M n p' q hp' ≫ (F.map (L.d p p').op).app (M.X q))

private def HomComplexNaturality_ff
    (C : Type u₂) [Category.{v₂} C] [Preadditive C]
    (F : Cᵒᵖ ⥤ C ⥤ C)
    (G : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (π : HomComplexProjection_ff C F G) :=
  ∀ {L L' M M'} (f : L' ⟶ L) (g : M ⟶ M') n p q (hpq : p + n = q),
    (((G.map f.op).app M) ≫ (G.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
      π L M n p q hpq ≫ (F.map (f.f p).op).app (M.X q) ≫
        (F.obj (op (L'.X p))).map (g.f q)

private def HomComplexZeroSource_ff
    (C : Type u₂) [Category.{v₂} C] [Preadditive C]
    (F : Cᵒᵖ ⥤ C ⥤ C)
    : Prop :=
  ∀ X Y, IsZero X → IsZero ((F.obj (op X)).obj Y)

private lemma isIso_dependent_generic_ff
    {D : Type*} [Category D] {Z : D} {B : ℤ → D}
    {k : ℤ} (π : ∀ q, k = q → (Z ⟶ B q)) {q : ℤ} (hq : k = q)
    (hi : IsIso (π k rfl)) : IsIso (π q hq) := by
  subst q
  exact hi

private def singleHomComplexGenericIso_ff
    {C : Type u₂} [Category.{v₂} C] [Preadditive C] [HasZeroObject C]
    {F : Cᵒᵖ ⥤ C ⥤ C} [∀ b, (F.obj b).PreservesZeroMorphisms]
    {G : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ}
    (proj : HomComplexProjection_ff C F G)
    (hlim : HomComplexLimit_ff C F G proj)
    (hdiff : HomComplexDifferential_ff C F G proj)
    (hzero : HomComplexZeroSource_ff C F) (L : C) (K : CochainComplex C ℤ) :
    (G.obj (op ((CochainComplex.singleFunctor C 0).obj L))).obj K ≅
      ((F.obj (op L)).mapHomologicalComplex (.up ℤ)).obj K := by
  classical
  let P := (CochainComplex.singleFunctor C 0).obj L
  let H := (G.obj (op P)).obj K
  let Q := fun n p : ℤ ↦ (F.obj (op (P.X p))).obj (K.X (p + n))
  let π := fun n p ↦ proj P K n p (p + n) rfl
  have hc (n : ℤ) : IsLimit (Fan.mk (H.X n) (π n)) := hlim P K n
  have hz (n p : ℤ) (h : p ≠ 0) : IsZero (Q n p) :=
    hzero _ _ (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 L p h)
  let v (n : ℤ) : Q n 0 ⟶ H.X n := Fan.IsLimit.lift (hc n)
    (fun p ↦ if h : p = 0 then eqToHom (congrArg (Q n) h.symm) else 0)
  have hv (n : ℤ) : v n ≫ π n 0 = 𝟙 (Q n 0) := by
    change Fan.IsLimit.lift (hc n) _ ≫ (Fan.mk (H.X n) (π n)).proj 0 = _
    rw [Fan.IsLimit.fac]
    simp
  have hπ (n : ℤ) : π n 0 ≫ v n = 𝟙 (H.X n) := by
    apply Fan.IsLimit.hom_ext (hc n)
    intro p
    change (π n 0 ≫ v n) ≫ π n p = 𝟙 (H.X n) ≫ π n p
    by_cases h : p = 0
    · subst p
      rw [Category.assoc, hv, Category.comp_id, Category.id_comp]
    · exact (hz n p h).eq_of_tgt _ _
  have hi (n : ℤ) : IsIso (proj P K n 0 n (Int.zero_add n)) := by
    have h := (Iso.mk (π n 0) (v n) (hπ n) (hv n)).isIso_hom
    exact isIso_dependent_generic_ff (fun q hq ↦ proj P K n 0 q hq) (Int.zero_add n) h
  let e (n : ℤ) : H.X n ≅ (F.obj (op L)).obj (K.X n) :=
    @asIso _ _ _ _ (proj P K n 0 n (Int.zero_add n)) (hi n)
  refine HomologicalComplex.Hom.isoOfComponents
    (C₁ := H) (C₂ := ((F.obj (op L)).mapHomologicalComplex (.up ℤ)).obj K) e ?_
  intro n m hnm
  have hm : m = n + 1 := hnm.symm
  subst m
  have hd := hdiff P K n (n + 1) 0 (n + 1)
    n 1 rfl (Int.zero_add _) (Int.zero_add _) (by omega)
  symm
  change H.d n (n + 1) ≫ proj P K (n + 1) 0 (n + 1) (Int.zero_add _) =
    proj P K n 0 n (Int.zero_add n) ≫ (F.obj (op L)).map (K.d n (n + 1))
  have hzero : (F.map (P.d 0 1).op).app (K.X (n + 1)) = 0 :=
    (hzero (P.X 1) _
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 L 1 (by decide))).eq_of_src _ _
  rw [hzero, comp_zero, smul_zero, sub_zero] at hd
  exact hd

private lemma singleHomComplexGenericIso_hom_f_ff
    {C : Type u₂} [Category.{v₂} C] [Preadditive C] [HasZeroObject C]
    {F : Cᵒᵖ ⥤ C ⥤ C} [∀ b, (F.obj b).PreservesZeroMorphisms]
    {G : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ}
    (proj : HomComplexProjection_ff C F G)
    (hlim : HomComplexLimit_ff C F G proj)
    (hdiff : HomComplexDifferential_ff C F G proj)
    (hzero : HomComplexZeroSource_ff C F) (L : C) (K : CochainComplex C ℤ) (n : ℤ) :
    (singleHomComplexGenericIso_ff proj hlim hdiff hzero L K).hom.f n =
      proj ((CochainComplex.singleFunctor C 0).obj L) K n 0 n (Int.zero_add n) := rfl

attribute [local irreducible] singleHomComplexGenericIso_ff

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def singleHomComplexGenericNatIso_ff
    {C : Type u₂} [Category.{v₂} C] [Preadditive C] [HasZeroObject C]
    {F : Cᵒᵖ ⥤ C ⥤ C} [∀ b, (F.obj b).PreservesZeroMorphisms]
    {G : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ}
    (proj : HomComplexProjection_ff C F G)
    (hlim : HomComplexLimit_ff C F G proj)
    (hdiff : HomComplexDifferential_ff C F G proj)
    (hzero : HomComplexZeroSource_ff C F)
    (hnatural : HomComplexNaturality_ff C F G proj) :
    ((CochainComplex.singleFunctor C 0).op.prod (𝟭 _)) ⋙ Functor.uncurry.obj G ≅
      Functor.uncurry.obj (mapComplexBifunctor_ff F) := by
  refine NatIso.ofComponents
    (fun P ↦ singleHomComplexGenericIso_ff proj hlim hdiff hzero P.1.unop P.2) ?_
  intro P Q f
  ext n : 1
  simp only [HomologicalComplex.comp_f, singleHomComplexGenericIso_hom_f_ff]
  change (((G.map ((CochainComplex.singleFunctor C 0).map f.1.unop).op).app P.2) ≫
      (G.obj _).map f.2).f n ≫ proj _ _ n 0 n (Int.zero_add n) =
    proj _ _ n 0 n (Int.zero_add n) ≫
      (F.map f.1).app (P.2.X n) ≫ (F.obj Q.1).map (f.2.f n)
  rw [hnatural]
  have hs : ((CochainComplex.singleFunctor C 0).map f.1.unop).f 0 = f.1.unop := by
    change (𝟙 _ ≫ f.1.unop ≫ 𝟙 _) = _
    simp only [Category.id_comp, Category.comp_id]
  erw [hs]
  rfl

namespace SiteHomComplex_ff
variable {T : Type (u + 1)} [Category.{u} T] {J : GrothendieckTopology T}
  [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  {R : Sheaf J CommRingCat.{u + 1}}

set_option hygiene false in
local notation "𝓡" => (sheafCompose J
  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R

private instance homAdditive (L : (SheafOfModules.{u + 1} 𝓡)ᵒᵖ) :
    ((SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R).obj L).Additive := by
  let F := (SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R).obj L
  have : PreservesLimitsOfSize.{0, 0} F :=
    (SheafOfModules.tensorHomAdjunction_kfg R L.unop).rightAdjoint_preservesLimits
  exact Functor.additive_of_preserves_binary_products F

omit [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
private theorem projectionNatural : HomComplexNaturality_ff
    (SheafOfModules.{u + 1} 𝓡)
    (SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R)
    (homComplexFunctor.{u + 1, u, u + 1, u + 1} (R := R))
    (homComplexπ.{u + 1, u, u + 1, u + 1} (R := R)) := by
  intro L L' M M' f g n p q h
  have h' := homComplexFunctor_map_f_π.{u + 1, u, u + 1, u + 1}
    (R := R) f g n p q h
  change _ = homComplexπ (R := R) _ _ n p q h ≫
    SheafOfModules.homObjMap (R := R) (f.f p) (𝟙 _) ≫
      SheafOfModules.homObjMap (R := R) (𝟙 _) (g.f q)
  erw [SheafOfModules.homObjMap_comp_homObjMap]
  simp only [Category.id_comp]
  exact h'

omit [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] in
private theorem homZeroSource : HomComplexZeroSource_ff
    (SheafOfModules.{u + 1} 𝓡)
    (SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R) := by
  intro X Y hX
  apply (IsZero.iff_id_eq_zero _).mpr
  change 𝟙 (SheafOfModules.homObj (R := R) X Y) = 0
  rw [← SheafOfModules.homObjMap_id (R := R), hX.eq_of_src (𝟙 _) 0]
  exact (((SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R).flip.obj Y).map_zero
    (op X) (op X))

private def comparison :
    ((CochainComplex.singleFunctor (SheafOfModules.{u + 1} 𝓡) 0).op.prod (𝟭 _)) ⋙
      Functor.uncurry.obj (homComplexFunctor.{u + 1, u, u + 1, u + 1} (R := R)) ≅
        Functor.uncurry.obj (mapComplexBifunctor_ff
          (SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R)) := by
  let F := SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R
  let : ∀ L, (F.obj L).PreservesZeroMorphisms := fun _ ↦ inferInstance
  exact singleHomComplexGenericNatIso_ff
    (F := SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R)
    (G := homComplexFunctor.{u + 1, u, u + 1, u + 1} (R := R))
    (homComplexπ.{u + 1, u, u + 1, u + 1} (R := R))
    (homComplexIsLimit.{u + 1, u, u + 1, u + 1} (R := R))
    (homComplex_d_π.{u + 1, u, u + 1, u + 1} (R := R))
    (homZeroSource (R := R)) (projectionNatural (R := R))

end SiteHomComplex_ff


private def bifunctorHomologyIso_ff
    {B : Type u₁} [Category.{v₁} B]
    {C : Type u₂} [Category.{v₂} C] [Preadditive C] [CategoryWithHomology C]
    {D : Type u₃} [Category.{v₃} D] [Preadditive D] [CategoryWithHomology D]
    (F : B ⥤ C ⥤ D) [∀ b, (F.obj b).PreservesZeroMorphisms]
    [∀ b, PreservesFiniteLimits (F.obj b)]
    [∀ b, PreservesFiniteColimits (F.obj b)] (r : ℤ) :
    Functor.uncurry.obj (mapComplexBifunctor_ff F) ⋙
        HomologicalComplex.homologyFunctor D (.up ℤ) r ≅
      ((𝟭 B).prod (HomologicalComplex.homologyFunctor C (.up ℤ) r)) ⋙
        Functor.uncurry.obj F := by
  refine NatIso.ofComponents (fun P ↦ (P.2.sc r).mapHomologyIso (F.obj P.1)) ?_
  intro P Q f
  let T := F.obj P.1
  let U := F.obj Q.1
  let τ : T ⟶ U := F.map f.1
  change HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app P.2 ≫
        (U.mapHomologicalComplex (.up ℤ)).map f.2) r ≫ ((Q.2.sc r).mapHomologyIso U).hom = _
  rw [HomologicalComplex.homologyMap_comp, Category.assoc]
  change ShortComplex.homologyMap ((P.2.sc r).mapNatTrans τ) ≫
      ShortComplex.homologyMap (U.mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) r).map f.2)) ≫
      ((Q.2.sc r).mapHomologyIso U).hom = _
  rw [ShortComplex.mapHomologyIso_hom_naturality]
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

private def bifunctorHomologyWhiskerIso_ff
    {A : Type*} [Category A]
    {B : Type u₁} [Category.{v₁} B]
    {C : Type u₂} [Category.{v₂} C] [Preadditive C] [CategoryWithHomology C]
    {D : Type u₃} [Category.{v₃} D] [Preadditive D] [CategoryWithHomology D]
    (F : B ⥤ C ⥤ D) [∀ b, (F.obj b).PreservesZeroMorphisms]
    (i : A ⥤ B)
    [∀ a, PreservesFiniteLimits (F.obj (i.obj a))]
    [∀ a, PreservesFiniteColimits (F.obj (i.obj a))] (r : ℤ) :
    i.prod (𝟭 _) ⋙ Functor.uncurry.obj (mapComplexBifunctor_ff F) ⋙
        HomologicalComplex.homologyFunctor D (.up ℤ) r ≅
      i.prod (HomologicalComplex.homologyFunctor C (.up ℤ) r) ⋙
        Functor.uncurry.obj F := by
  let : ∀ a, ((i ⋙ F).obj a).PreservesZeroMorphisms := fun a ↦
    (inferInstance : (F.obj (i.obj a)).PreservesZeroMorphisms)
  let : ∀ a, PreservesFiniteLimits ((i ⋙ F).obj a) := fun a ↦
    (inferInstance : PreservesFiniteLimits (F.obj (i.obj a)))
  let : ∀ a, PreservesFiniteColimits ((i ⋙ F).obj a) := fun a ↦
    (inferInstance : PreservesFiniteColimits (F.obj (i.obj a)))
  exact bifunctorHomologyIso_ff (i ⋙ F) r

private theorem descendBifunctorIso_ff
    {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]
    {K : Type*} [Category K]
    (W : MorphismProperty K) [W.ContainsIdentities] (Q : K ⥤ D) [Q.IsLocalization W]
    (i : A ⥤ B) (I : K ⥤ K) (H : K ⥤ C) (HD : D ⥤ C)
    (eη : H ≅ I ⋙ H) (eH : Q ⋙ HD ≅ H)
    (F : B ⥤ C ⥤ C) (G : B × D ⥤ C) (T : B × K ⥤ C)
    (e : ((𝟭 B).prod Q) ⋙ G ≅ ((𝟭 B).prod I) ⋙ T)
    (eT : i.prod (𝟭 K) ⋙ T ≅ i.prod H ⋙ Functor.uncurry.obj F) :
    Nonempty ((i.prod (𝟭 D)) ⋙ G ≅
      (i.prod HD) ⋙ Functor.uncurry.obj F) := by
  let WA := MorphismProperty.isomorphisms A
  let : (𝟭 A).IsLocalization WA := Functor.IsLocalization.for_id WA le_rfl
  let e₁ := Functor.isoWhiskerLeft (i.prod (𝟭 K)) e
  let e₂ := Functor.isoWhiskerLeft ((𝟭 A).prod I) eT
  let e₃ := Functor.isoWhiskerRight (NatIso.prod (Iso.refl i) eη.symm)
    (Functor.uncurry.obj F)
  let e₄ := Functor.isoWhiskerRight (NatIso.prod (Iso.refl i) eH.symm)
    (Functor.uncurry.obj F)
  exact ⟨(Localization.fullyFaithfulWhiskeringLeft ((𝟭 A).prod Q)
    (WA.prod W) C).preimageIso (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄)⟩

private def resolutionHomologyIso_ff
    {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [CategoryWithHomology C]
    (I : CochainComplex C ℤ ⥤ CochainComplex C ℤ) (η : 𝟭 _ ⟶ I)
    (hη : ∀ K, QuasiIso (η.app K)) (r : ℤ) :
    HomologicalComplex.homologyFunctor C (.up ℤ) r ≅
      I ⋙ HomologicalComplex.homologyFunctor C (.up ℤ) r := by
  let H := HomologicalComplex.homologyFunctor C (.up ℤ) r
  let ηH : H ⟶ I ⋙ H := Functor.whiskerRight η H
  have : IsIso ηH := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    let := hη K
    change IsIso (HomologicalComplex.homologyMap (η.app K) r)
    infer_instance
  exact asIso ηH

private abbrev finiteLocalSystemProperty (S : Scheme.{u}) (A : Type u) [Field A] :
    ObjectProperty (proEtaleRingModules S (proEtaleConstantRing S A)) :=
  IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
    (fun M ↦ Module.Finite (ULift.{u + 1} A) M)

private abbrev finiteLocalSystemInclusion (S : Scheme.{u}) (A : Type u) [Field A] :=
  ObjectProperty.ι (finiteLocalSystemProperty S A)

private instance finiteLocalSystemFree (S : Scheme.{u}) (A : Type u) [Field A]
    (L : (finiteLocalSystemProperty S A).FullSubcategory) : L.obj.IsFiniteLocallyFree :=
  finiteModelsLocallyFree S A L.obj L.property

private instance finiteLocalSystemHomLimits (S : Scheme.{u}) (A : Type u) [Field A]
    (L : (finiteLocalSystemProperty S A).FullSubcategory) :
    PreservesFiniteLimits
      ((SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1}
        (proEtaleConstantRing S A)).obj (op L.obj)) :=
  finiteLocallyFreeHomLimits S A L.obj

private instance finiteLocalSystemHomColimits (S : Scheme.{u}) (A : Type u) [Field A]
    (L : (finiteLocalSystemProperty S A).FullSubcategory) :
    PreservesFiniteColimits
      ((SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1}
        (proEtaleConstantRing S A)).obj (op L.obj)) := by
  have := finiteLocallyFreeHomColimits S A L.obj
  infer_instance

private def singleDerivedHomologyIso_ff
    {A : Type u₁} [Category.{v₁} A] {C : Type u₂} [Category.{v₂} C]
    {D : Type u₃} [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E]
    (Q : C ⥤ D) (s : A ⥤ C) (sd : A ⥤ D) (es : sd ≅ s ⋙ Q)
    (I : C ⥤ C) (RH : Dᵒᵖ × D ⥤ D) (G : Cᵒᵖ × C ⥤ C)
    (T : Aᵒᵖ × C ⥤ C) (HD : D ⥤ E) (HC : C ⥤ E)
    (e : (Q.op.prod Q) ⋙ RH ≅ ((𝟭 Cᵒᵖ).prod I) ⋙ G ⋙ Q)
    (et : (s.op.prod (𝟭 C)) ⋙ G ≅ T) (eh : Q ⋙ HD ≅ HC) :
    ((𝟭 Aᵒᵖ).prod Q) ⋙ (sd.op.prod (𝟭 D)) ⋙ RH ⋙ HD ≅
      ((𝟭 Aᵒᵖ).prod I) ⋙ T ⋙ HC := by
  let j := s.op.prod (𝟭 C)
  let e₀ : ((𝟭 Aᵒᵖ).prod Q) ⋙ (sd.op.prod (𝟭 D)) ≅ j ⋙ Q.op.prod Q :=
    NatIso.prod (NatIso.op es).symm (Iso.refl Q)
  exact Functor.isoWhiskerRight e₀ (RH ⋙ HD) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft j e) HD ≪≫
    Functor.isoWhiskerLeft (j ⋙ ((𝟭 Cᵒᵖ).prod I) ⋙ G) eh ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft ((𝟭 Aᵒᵖ).prod I) et) HC

private def combineDualTensorIso_ff
    {B : Type u₁} [Category.{v₁} B] {C : Type u₂} [Category.{v₂} C]
    {D : Type u₃} [Category.{v₃} D]
    (i : B ⥤ Cᵒᵖ) (U : Cᵒᵖ ⥤ C) (H : Cᵒᵖ × C ⥤ C)
    (T : C × C ⥤ C) (h : D ⥤ C) (F : Cᵒᵖ × D ⥤ C)
    (eH : (i.prod (𝟭 D)) ⋙ F ≅ (i.prod h) ⋙ H)
    (eE : ((i ⋙ U).prod (𝟭 C)) ⋙ T ≅ (i.prod (𝟭 C)) ⋙ H) :
    (i.prod (𝟭 D)) ⋙ F ≅ (i.prod (𝟭 D)) ⋙ (U.prod h) ⋙ T := by
  exact eH ≪≫ Functor.isoWhiskerLeft ((𝟭 B).prod h) eE.symm

private theorem exactSourceDerivedHomCore_ff
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{u₂} C]
    (F : Cᵒᵖ ⥤ C ⥤ C) [∀ L, (F.obj L).PreservesZeroMorphisms]
    (G : (CochainComplex C ℤ)ᵒᵖ × CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (RH : (DerivedCategory.{u₂} C)ᵒᵖ × DerivedCategory.{u₂} C ⥤ DerivedCategory.{u₂} C)
    (P : ObjectProperty C)
    (hlim : ∀ L : P.FullSubcategory, PreservesFiniteLimits (F.obj (op L.obj)))
    (hcolim : ∀ L : P.FullSubcategory, PreservesFiniteColimits (F.obj (op L.obj)))
    (r : ℤ) (I : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (η : 𝟭 _ ⟶ I) (hI : ∀ K, QuasiIso (η.app K))
    (eR : (DerivedCategory.Q.op.prod DerivedCategory.Q) ⋙ RH ≅
      ((𝟭 (CochainComplex C ℤ)ᵒᵖ).prod I) ⋙ G ⋙ DerivedCategory.Q)
    (eSingle : ((CochainComplex.singleFunctor C 0).op.prod (𝟭 _)) ⋙ G ≅
      Functor.uncurry.obj (mapComplexBifunctor_ff F)) :
    Nonempty (
      ((ObjectProperty.ι P).op.prod (𝟭 _)) ⋙
        ((DerivedCategory.singleFunctor C 0).op.prod (𝟭 _)) ⋙ RH ⋙
          DerivedCategory.homologyFunctor C r ≅
      ((ObjectProperty.ι P).op.prod (DerivedCategory.homologyFunctor C r)) ⋙
        Functor.uncurry.obj F) := by
  let i := (ObjectProperty.ι P).op
  let : ∀ b : P.FullSubcategoryᵒᵖ,
      PreservesFiniteLimits (F.obj (i.obj b)) := fun b ↦ hlim b.unop
  let : ∀ b : P.FullSubcategoryᵒᵖ,
      PreservesFiniteColimits (F.obj (i.obj b)) := fun b ↦ hcolim b.unop
  let eC := singleDerivedHomologyIso_ff
    (DerivedCategory.Q (C := C)) (CochainComplex.singleFunctor C 0)
    (DerivedCategory.singleFunctor C 0) (DerivedCategory.singleFunctorIsoCompQ C 0)
    I RH G (Functor.uncurry.obj (mapComplexBifunctor_ff F))
    (DerivedCategory.homologyFunctor C r)
    (HomologicalComplex.homologyFunctor C (.up ℤ) r)
    eR eSingle (DerivedCategory.homologyFunctorFactors C r)
  exact descendBifunctorIso_ff (HomologicalComplex.quasiIso C (.up ℤ))
    (DerivedCategory.Q (C := C)) i I
    (HomologicalComplex.homologyFunctor C (.up ℤ) r)
    (DerivedCategory.homologyFunctor C r)
    (resolutionHomologyIso_ff I η hI r) (DerivedCategory.homologyFunctorFactors C r)
    F (((DerivedCategory.singleFunctor C 0).op.prod (𝟭 _)) ⋙ RH ⋙
      DerivedCategory.homologyFunctor C r)
    (Functor.uncurry.obj (mapComplexBifunctor_ff F) ⋙
      HomologicalComplex.homologyFunctor C (.up ℤ) r) eC
    (bifunctorHomologyWhiskerIso_ff F i r)

private def uncurryMapWithPreadditive_ff
    {B : Type u₁} [Category.{v₁} B] (C : Type u₂) [Category.{v₂} C]
    (p : Preadditive C) (F : B ⥤ C ⥤ C)
    (h : letI := p; ∀ b, (F.obj b).PreservesZeroMorphisms) :=
  letI := p
  letI := h
  Functor.uncurry.obj (mapComplexBifunctor_ff F)

private theorem uncurryMapWithPreadditive_heq_ff
    {B : Type u₁} [Category.{v₁} B] (C : Type u₂) [Category.{v₂} C]
    [Subsingleton (Preadditive C)] (p p' : Preadditive C) (F : B ⥤ C ⥤ C)
    (h : letI := p; ∀ b, (F.obj b).PreservesZeroMorphisms)
    (h' : letI := p'; ∀ b, (F.obj b).PreservesZeroMorphisms) :
    HEq (uncurryMapWithPreadditive_ff C p F h)
      (uncurryMapWithPreadditive_ff C p' F h') := by
  have e : p = p' := Subsingleton.elim _ _
  subst p'
  rfl

attribute [local irreducible] derivedInternalHomOfUniverses

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace SiteHomComplex_ff

variable {T : Type (u + 1)} [Category.{u} T] {J : GrothendieckTopology T}
  [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  (R : Sheaf J CommRingCat.{u + 1})

set_option hygiene false in
local notation "𝓡" => (sheafCompose J
  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R

private theorem uncurryMap_coherent_ff
    (F : (SheafOfModules.{u + 1} 𝓡)ᵒᵖ ⥤
      SheafOfModules.{u + 1} 𝓡 ⥤ SheafOfModules.{u + 1} 𝓡)
    (h : letI : Preadditive (SheafOfModules.{u + 1} 𝓡) :=
        (SheafOfModules.instAbelian 𝓡).toPreadditive
      ∀ L, (F.obj L).PreservesZeroMorphisms)
    (h' : letI : Preadditive (SheafOfModules.{u + 1} 𝓡) :=
        SheafOfModules.instPreadditive 𝓡
      ∀ L, (F.obj L).PreservesZeroMorphisms) :
    (letI : Preadditive (SheafOfModules.{u + 1} 𝓡) :=
      (SheafOfModules.instAbelian 𝓡).toPreadditive
     letI := h
     Functor.uncurry.obj (mapComplexBifunctor_ff F)) =
    (letI : Preadditive (SheafOfModules.{u + 1} 𝓡) :=
      SheafOfModules.instPreadditive 𝓡
     letI := h'
     Functor.uncurry.obj (mapComplexBifunctor_ff F)) := by
  let M := SheafOfModules.{u + 1} 𝓡
  let p := (SheafOfModules.instAbelian 𝓡 : Abelian M).toPreadditive
  let p' : Preadditive M := SheafOfModules.instPreadditive 𝓡
  let : HasFiniteBiproducts M := HasFiniteBiproducts.of_hasFiniteProducts
  exact eq_of_heq (uncurryMapWithPreadditive_heq_ff M p p' F h h')

open SheafOfModules in
private theorem exactSourceDerivedHomIso
    [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1} 𝓡)]
    (P : ObjectProperty (SheafOfModules.{u + 1} 𝓡))
    (hlim : ∀ L : P.FullSubcategory, PreservesFiniteLimits
      ((SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R).obj (op L.obj)))
    (hcolim : ∀ L : P.FullSubcategory, PreservesFiniteColimits
      ((SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R).obj (op L.obj)))
    (r : ℤ) :
    Nonempty (
      ((ObjectProperty.ι P).op.prod (𝟭 _)) ⋙
        ((DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2}
          (SheafOfModules.{u + 1} 𝓡) 0).op.prod (𝟭 _)) ⋙
        derivedInternalHomOfUniverses.{u + 1, u, u + 1, u + 2} J R ⋙
        DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2}
          (SheafOfModules.{u + 1} 𝓡) r ≅
      ((ObjectProperty.ι P).op.prod
        (DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2}
          (SheafOfModules.{u + 1} 𝓡) r)) ⋙
        Functor.uncurry.obj (SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R)) := by
  let M := SheafOfModules.{u + 1} 𝓡
  let F := SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R
  let i := (ObjectProperty.ι P).op
  let : ∀ L, (F.obj L).PreservesZeroMorphisms := fun L ↦ inferInstance
  let : ∀ b : P.FullSubcategoryᵒᵖ,
      PreservesFiniteLimits (F.obj (i.obj b)) := fun b ↦ hlim b.unop
  let : ∀ b : P.FullSubcategoryᵒᵖ,
      PreservesFiniteColimits (F.obj (i.obj b)) := fun b ↦ hcolim b.unop
  obtain ⟨I, η, hI⟩ :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
      J R).2.2
  obtain ⟨eR⟩ :=
    derivedInternalHomOfUniverses_comparison.{u + 1, u, u + 1, u + 2} J R I η
      (fun K ↦ ⟨(hI K).1, (hI K).2.1⟩)
  let eSingle := comparison (R := R) ≪≫
    eqToIso (uncurryMap_coherent_ff (R := R) F
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)).symm
  obtain ⟨e⟩ := exactSourceDerivedHomCore_ff F
    (Functor.uncurry.obj (homComplexFunctor.{u + 1, u, u + 1, u + 1} (R := R)))
    (derivedInternalHomOfUniverses.{u + 1, u, u + 1, u + 2} J R) P
    hlim hcolim r I η (fun K ↦ (hI K).1) eR eSingle
  refine ⟨NatIso.ofComponents (fun X ↦ e.app X) ?_⟩
  intro X Y f
  exact e.hom.naturality f


private theorem dualTensorDerivedHomIso
    [HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1} 𝓡)]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (P : ObjectProperty (SheafOfModules.{u + 1} 𝓡))
    (hlim : ∀ L : P.FullSubcategory, PreservesFiniteLimits
      ((SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R).obj (op L.obj)))
    (hcolim : ∀ L : P.FullSubcategory, PreservesFiniteColimits
      ((SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R).obj (op L.obj)))
    (hfree : ∀ L : P.FullSubcategory, L.obj.IsFiniteLocallyFree) (r : ℤ) :
    Nonempty (
      ((ObjectProperty.ι P).op.prod (𝟭 _)) ⋙
        ((DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2}
          (SheafOfModules.{u + 1} 𝓡) 0).op.prod (𝟭 _)) ⋙
        derivedInternalHomOfUniverses.{u + 1, u, u + 1, u + 2} J R ⋙
        DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2}
          (SheafOfModules.{u + 1} 𝓡) r ≅
      ((ObjectProperty.ι P).op.prod (𝟭 _)) ⋙
        (((SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R).flip.obj
          (SheafOfModules.unit 𝓡)).prod
          (DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2}
            (SheafOfModules.{u + 1} 𝓡) r)) ⋙
          Functor.uncurry.obj (curriedTensor (SheafOfModules.{u + 1} 𝓡))) := by
  let M := SheafOfModules.{u + 1} 𝓡
  let i := (ObjectProperty.ι P).op
  let HF := SheafOfModules.homFunctor.{u + 1, u, u + 1, u + 1} R
  let U := HF.flip.obj (SheafOfModules.unit 𝓡)
  let HD := DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} M r
  obtain ⟨eH⟩ := exactSourceDerivedHomIso (R := R) P hlim hcolim r
  obtain ⟨τ, hτ⟩ := SheafOfModules.evaluationNat_exists_ff (R := R)
  let eE := restrictTensorEvaluationIso_ff i
    (SheafOfModules.dualFunctor_ff (R := R)) HF τ
    (fun L N ↦ hτ L.unop.obj N (hfree L.unop))
  let eResult := combineDualTensorIso_ff i U (Functor.uncurry.obj HF)
    (Functor.uncurry.obj (curriedTensor M)) HD
    (((DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2} M 0).op.prod (𝟭 _)) ⋙
      derivedInternalHomOfUniverses.{u + 1, u, u + 1, u + 2} J R ⋙ HD) eH eE
  refine ⟨NatIso.ofComponents (fun X ↦ eResult.app X) ?_⟩
  intro X Y f
  exact eResult.hom.naturality f


end SiteHomComplex_ff

private def restrictPairNatIso_ff
    {B : Type u₁} [Category.{v₁} B] {C : Type u₂} [Category.{v₂} C]
    {D : Type u₃} [Category.{v₃} D]
    (P : ObjectProperty B) (Q : ObjectProperty (Bᵒᵖ × D))
    (h : ∀ X, Q X → P X.1.unop) (F G : Bᵒᵖ × D ⥤ C)
    (e : (((ObjectProperty.ι P).op).prod (𝟭 D)) ⋙ F ≅
      (((ObjectProperty.ι P).op).prod (𝟭 D)) ⋙ G) :
    ObjectProperty.ι Q ⋙ F ≅ ObjectProperty.ι Q ⋙ G := by
  let j : Q.FullSubcategory ⥤ P.FullSubcategoryᵒᵖ × D :=
    { obj X := (op ⟨X.obj.1.unop, h X.obj X.property⟩, X.obj.2)
      map f := Prod.mkHom (ObjectProperty.homMk f.hom.1.unop).op f.hom.2
      map_id X := rfl
      map_comp f g := rfl }
  exact Functor.isoWhiskerLeft j e


attribute [local irreducible] DerivedCategory.homologyFunctor SheafOfModules.homFunctor

private theorem finiteLocalSystemDualTensorIso (S : Scheme.{u}) (A : Type u) [Field A]
    (r : ℤ) :
    Nonempty (
    ((finiteLocalSystemInclusion S A).op.prod (𝟭 _)) ⋙
      finiteFieldInternalHomCohomology S A r ≅
    ((finiteLocalSystemInclusion S A).op.prod (𝟭 _)) ⋙
      finiteFieldDualTensorCohomology S A r) := by
  obtain ⟨e⟩ := SiteHomComplex_ff.dualTensorDerivedHomIso (proEtaleConstantRing S A)
    (finiteLocalSystemProperty S A)
    (fun L ↦ finiteLocalSystemHomLimits S A L)
    (fun L ↦ finiteLocalSystemHomColimits S A L)
    (fun L ↦ finiteLocalSystemFree S A L) r
  refine ⟨NatIso.ofComponents (fun X ↦ e.app X) ?_⟩
  intro X Y f
  exact e.hom.naturality f


attribute [local semireducible] SheafOfModules.homFunctor
attribute [local irreducible] finiteFieldInternalHomCohomology

/-- Internal Hom from a finite-dimensional local system preserves constructible
cohomology and the same finite cohomological interval. The second conjunct supplies
cohomology isomorphisms natural in both variables on the full subcategory of pairs
consisting of a finite local system and a bounded constructible complex.

Source: Bhatt--Scholze, Lemma 6.7.13, finite-coefficient local-system case;
Stacks Project, Tag 0FNY, example-dual
(blueprint: lem-sfb-finite-field-lisse-internal-hom).

Proof:
1. Choose finite bases on the given local constant models. The additive constant-module
sheafification functor carries the basis isomorphisms to finite free slice charts. The
slice internal-Hom comparison identifies the dual with the same finite local models.
2. The presheaf evaluation map sends a pure tensor of a dual functional and a section
of M to their scalar product. The dual-basis expansion proves this map bijective over
every object mapping to a free chart. Sheafification makes it an isomorphism of sheaves.
Precomposition and postcomposition give naturality in both variables.
3. Evaluation identifies internal Hom from L with tensoring by its dual. The
tensor-Hom adjunction therefore gives preservation of colimits. Internal Hom also
preserves limits by the same adjunction and is additive, hence it is exact. The Hom complex
from L[0]
projects isomorphically onto its only nonzero source-degree factor, the termwise Hom
complex. The product universal property proves the inverse and the differential formula
proves compatibility with differentials. All these comparisons are natural.
4. Compute derived Hom on the functorial K-injective resolution. Exactness commutes
with homology. Cancel the homology isomorphism of the resolution, then descend the
comparison through identity times the derived localization. Compose with inverse
evaluation to obtain the natural dual-tensor cohomology formula for arbitrary complexes.
5. Finite-dimensional modules over the finite field are finite sets. The constant
scalar comparison and the proved constructible tensor helper show that the tensor of
the finite local dual with each constructible cohomology sheaf is constructible.
Outside the given interval the latter sheaf is zero, and additive Hom preserves zero
objects. Transport these assertions through the comparison and restrict its naturality
to the full subcategory of admissible pairs. The empty scheme, rank zero and a=b are
included without any exception. -/
theorem finiteField_lisse_internalHom
    (S : Scheme.{u}) [IsLocallyNoetherian S] [CompactSpace S]
    (A : Type u) [Field A] [Finite A] :
    (∀ (L : proEtaleRingModules S (proEtaleConstantRing S A)),
      IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
        (fun M ↦ Module.Finite (ULift.{u + 1, u} A) M) L →
      ∀ (a b : ℤ), a ≤ b →
      ∀ (N : DerivedCategory.{u + 2} (proEtaleRingModules S (proEtaleConstantRing S A))),
        (∀ r : ℤ, IsConstructibleProEtaleModuleSheaf S A
          ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ r).obj N)) →
        (∀ r : ℤ, r < a ∨ b < r →
          IsZero ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2}
      (proEtaleRingModules S (proEtaleConstantRing S A)) r).obj N)) →
        ∀ r : ℤ,
          IsConstructibleProEtaleModuleSheaf S A
            ((finiteFieldInternalHomCohomology S A r).obj (op L, N)) ∧
          (r < a ∨ b < r →
            IsZero ((finiteFieldInternalHomCohomology S A r).obj (op L, N)))) ∧
    ∀ r : ℤ, Nonempty (
      (ObjectProperty.ι (fun P :
          (proEtaleRingModules S (proEtaleConstantRing S A))ᵒᵖ ×
            DerivedCategory.{u + 2} (proEtaleRingModules S (proEtaleConstantRing S A)) ↦
        IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
          (fun M ↦ Module.Finite (ULift.{u + 1, u} A) M) P.1.unop ∧
        (∀ q : ℤ, IsConstructibleProEtaleModuleSheaf S A
          ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ q).obj P.2)) ∧
        ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
          IsZero ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ q).obj P.2))) ⋙
            finiteFieldInternalHomCohomology S A r ≅
      (ObjectProperty.ι (fun P :
          (proEtaleRingModules S (proEtaleConstantRing S A))ᵒᵖ ×
            DerivedCategory.{u + 2} (proEtaleRingModules S (proEtaleConstantRing S A)) ↦
        IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
          (fun M ↦ Module.Finite (ULift.{u + 1, u} A) M) P.1.unop ∧
        (∀ q : ℤ, IsConstructibleProEtaleModuleSheaf S A
          ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ q).obj P.2)) ∧
        ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
          IsZero ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ q).obj P.2))) ⋙
            finiteFieldDualTensorCohomology S A r) := by
  constructor
  · intro L hL a b _hab N hN hz r
    let LL : (finiteLocalSystemProperty S A).FullSubcategory := ⟨L, hL⟩
    obtain ⟨eNat⟩ := finiteLocalSystemDualTensorIso S A r
    let e : (finiteFieldInternalHomCohomology S A r).obj (op L, N) ≅
        SheafOfModules.homObj (R := proEtaleConstantRing S A) L (SheafOfModules.unit _) ⊗
          ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ r).obj N) :=
      eNat.app (op LL, N)
    have hc := finiteModelsTensorConstructible S A
      (SheafOfModules.homObj (R := proEtaleConstantRing S A) L (SheafOfModules.unit _))
      ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ r).obj N)
      (dualFiniteModels S A L hL) (hN r)
    constructor
    · apply (proEtaleModuleRestriction_constructible_iff S A _).mpr
      exact ProEtale.isConstructible_of_iso
        ((proEtaleModuleRestriction S A).mapIso e).symm
        ((proEtaleModuleRestriction_constructible_iff S A _).mp hc)
    · intro hr
      let : L.IsFiniteLocallyFree := finiteModelsLocallyFree S A L hL
      obtain ⟨eEval⟩ := SheafOfModules.finiteFreeEvaluationIso_ff
        (R := proEtaleConstantRing S A) L
      let eH : (finiteFieldInternalHomCohomology S A r).obj (op L, N) ≅
          SheafOfModules.homObj (R := proEtaleConstantRing S A) L
            ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ r).obj N) :=
        e ≪≫ eEval.app _
      have h0 := ((SheafOfModules.homFunctor
        (proEtaleConstantRing S A)).obj (op L)).map_isZero (hz r hr)
      exact h0.of_iso eH
  · intro r
    let M := proEtaleRingModules S (proEtaleConstantRing S A)
    let P : ObjectProperty (Mᵒᵖ × DerivedCategory.{u + 2} M) := fun P ↦
      finiteLocalSystemProperty S A P.1.unop ∧
        (∀ q : ℤ, IsConstructibleProEtaleModuleSheaf S A
          ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} M q).obj P.2)) ∧
        ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
          IsZero ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} M q).obj P.2)
    obtain ⟨eNat⟩ := finiteLocalSystemDualTensorIso S A r
    exact ⟨restrictPairNatIso_ff (finiteLocalSystemProperty S A) P
      (fun _ h ↦ h.1) (finiteFieldInternalHomCohomology S A r)
      (finiteFieldDualTensorCohomology S A r) eNat⟩

end AlgebraicGeometry.Scheme
