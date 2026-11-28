/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompletePullbackReduction
import WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageConeTowerStrictness
import all WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageRoosLimitData
import all WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare

/-! # Finite levels of the direct-image reduction mate

## Implementation details

Pasting the reduction mate with the evaluation mate `pushEvaluationMap` gives the module-level
mate of the finite reduction comparison `red ⋙ dev n`. On a K-injective complex `I` this mate is
represented by the ordinary mate of the strict cone comparison, evaluated at level `n`. That
ordinary mate is an isomorphism in every degree, because it is compatible with both summands of
the mapping cone and the direct image is additive.

## References

* Stacks Project, Tag 0944
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject
  AdicCompletion.ringCommutative AdicCompletion.modulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

namespace LevelwiseIso

open TwoSquare

/-- Module inverse image. -/
private abbrev H := CondensedRing.upperStar (DerivedNakayama.integerRing l E) f

/-- Module direct image. -/
private abbrev P := CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f

/-- The ordinary inverse-image/direct-image adjunction. -/
private abbrev adj := CondensedRing.upperStarLowerStarAdjunction (DerivedNakayama.integerRing l E) f

/-- The finite reduction functor at level `n`. -/
private def C (T : Scheme.{u}) (n : ℕ) :
    DerivedCategory (AdicCompletion.Modules l E T) ⥤
      DerivedCategory (AdicCompletion.Modules l E T) :=
  red l E T ⋙ dev l E T n

/-- The strict model of the finite reduction functor at level `n`. -/
private def Φ (T : Scheme.{u}) (n : ℕ) :
    CochainComplex (AdicCompletion.Modules l E T) ℤ ⥤
      CochainComplex (AdicCompletion.Modules l E T) ℤ :=
  strictRed l E T ⋙ (ev l E T n).mapHomologicalComplex (.up ℤ)

/-- The finite reduction functor computed on the strict model, at a complex. -/
private def eI (T : Scheme.{u}) (n : ℕ) (M : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    (C l E T n).obj (DerivedCategory.Q.obj M) ≅ DerivedCategory.Q.obj ((Φ l E T n).obj M) :=
  (dev l E T n).mapIso ((redFactors l E T).app M) ≪≫
    (ev l E T n).mapDerivedCategoryFactors.app ((strictRed l E T).obj M)

private theorem eI_naturality (T : Scheme.{u}) (n : ℕ)
    {M N : CochainComplex (AdicCompletion.Modules l E T) ℤ} (g : M ⟶ N) :
    (C l E T n).map (DerivedCategory.Q.map g) ≫ (eI l E T n N).hom =
      (eI l E T n M).hom ≫ DerivedCategory.Q.map ((Φ l E T n).map g) := by
  have h : (dev l E T n).map ((red l E T).map (DerivedCategory.Q.map g)) ≫
      (dev l E T n).map ((redFactors l E T).hom.app N) ≫
      (ev l E T n).mapDerivedCategoryFactors.hom.app ((strictRed l E T).obj N) =
      ((dev l E T n).map ((redFactors l E T).hom.app M) ≫
        (ev l E T n).mapDerivedCategoryFactors.hom.app ((strictRed l E T).obj M)) ≫
      DerivedCategory.Q.map (((ev l E T n).mapHomologicalComplex (.up ℤ)).map
        ((strictRed l E T).map g)) := by
    rw [← Functor.map_comp_assoc]
    erw [(redFactors l E T).hom.naturality g]
    rw [Functor.map_comp_assoc]
    erw [(ev l E T n).mapDerivedCategoryFactors_hom_naturality]
    rw [Category.assoc]
  exact h

/-- The strict pullback comparison of the finite reductions. -/
private def s (n : ℕ) :
    Φ l E Y n ⋙ (H l E f).mapHomologicalComplex (.up ℤ) ⟶
      (H l E f).mapHomologicalComplex (.up ℤ) ⋙ Φ l E X n where
  app M := ((ev l E X n).mapHomologicalComplex (.up ℤ)).map
    ((strictPullReduction l E f).hom.app M)
  naturality _ _ g := by
    have h := congrArg ((ev l E X n).mapHomologicalComplex (.up ℤ)).map
      ((strictPullReduction l E f).hom.naturality g)
    simp only [Functor.map_comp] at h
    exact h

/-- The derived pullback comparison of the finite reductions. -/
private def ψ (n : ℕ) :
    TwoSquare (C l E Y n) (dpullModule l E f) (dpullModule l E f) (C l E X n) :=
  TwoSquare.mk _ _ _ _ (pullReduction l E f).hom ≫ₕ
    TwoSquare.mk _ _ _ _ (pullEvaluation l E f n).inv

/-- The module-level mate of `ψ`. -/
private def φ (n : ℕ) :=
  mateEquiv (moduleAdjunction l E f) (moduleAdjunction l E f) (ψ l E f n)

/-- The ordinary mate of the strict comparison. -/
private def m (n : ℕ) :=
  mateEquiv ((adj l E f).mapHomologicalComplex (.up ℤ))
    ((adj l E f).mapHomologicalComplex (.up ℤ)) (TwoSquare.mk _ _ _ _ (s l E f n))

private theorem ψ_naturality (n : ℕ) {M N : DerivedCategory (AdicCompletion.Modules l E Y)}
    (g : M ⟶ N) :
    (dpullModule l E f).map ((C l E Y n).map g) ≫ (ψ l E f n).app N =
      (ψ l E f n).app M ≫ (C l E X n).map ((dpullModule l E f).map g) :=
  (ψ l E f n).naturality g

private theorem φ_counit (n : ℕ) (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    (dpullModule l E f).map ((φ l E f n).app K) ≫
        (moduleAdjunction l E f).counit.app ((C l E X n).obj K) =
      (ψ l E f n).app ((rpushModule l E f).obj K) ≫
        (C l E X n).map ((moduleAdjunction l E f).counit.app K) :=
  mateEquiv_counit _ _ (ψ l E f n) K

private theorem m_counit (n : ℕ) (I : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    ((H l E f).mapHomologicalComplex (.up ℤ)).map ((m l E f n).app I) ≫
      ((adj l E f).mapHomologicalComplex (.up ℤ)).counit.app ((Φ l E X n).obj I) =
      (s l E f n).app (((P l E f).mapHomologicalComplex (.up ℤ)).obj I) ≫ (Φ l E X n).map
        (((adj l E f).mapHomologicalComplex (.up ℤ)).counit.app I) :=
  mateEquiv_counit _ _ (TwoSquare.mk _ _ _ _ (s l E f n)) I

private theorem cochain_counit' (I : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    (dpullModule l E f).map (UnboundedExactTower.cochainUnit (P l E f) I) ≫
        (moduleAdjunction l E f).counit.app (DerivedCategory.Q.obj I) =
      (H l E f).mapDerivedCategoryFactors.hom.app
          (((P l E f).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map (((adj l E f).mapHomologicalComplex (.up ℤ)).counit.app I) :=
  UnboundedExactTower.cochain_counit (adj l E f) I

private theorem ψ_normalization_aux (n : ℕ)
    (M : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    (dpullModule l E f).map ((ev l E Y n).mapDerivedCategoryFactors.inv.app
        ((strictRed l E Y).obj M)) ≫
      (dpullModule l E f).map ((dev l E Y n).map ((redFactors l E Y).inv.app M)) ≫
      (pullEvaluation l E f n).inv.app ((red l E Y).obj (DerivedCategory.Q.obj M)) ≫
      (dev l E X n).map ((pullReduction l E f).hom.app (DerivedCategory.Q.obj M)) ≫
      (dev l E X n).map ((red l E X).map ((H l E f).mapDerivedCategoryFactors.hom.app M)) ≫
      (dev l E X n).map ((redFactors l E X).hom.app
        (((H l E f).mapHomologicalComplex (.up ℤ)).obj M)) ≫
      (ev l E X n).mapDerivedCategoryFactors.hom.app
        ((strictRed l E X).obj (((H l E f).mapHomologicalComplex (.up ℤ)).obj M)) =
      (H l E f).mapDerivedCategoryFactors.hom.app
          (((ev l E Y n).mapHomologicalComplex (.up ℤ)).obj ((strictRed l E Y).obj M)) ≫
        DerivedCategory.Q.map (((ev l E X n).mapHomologicalComplex (.up ℤ)).map
          ((strictPullReduction l E f).hom.app M)) := by
  let K := (strictRed l E Y).obj M
  let r := (redFactors l E Y).inv.app M
  have hpr : (dpull l E f).map r ≫ (pullReduction l E f).hom.app (DerivedCategory.Q.obj M) ≫
      (red l E X).map ((H l E f).mapDerivedCategoryFactors.hom.app M) ≫
      (redFactors l E X).hom.app (((H l E f).mapHomologicalComplex (.up ℤ)).obj M) =
      (pull l E f).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((strictPullReduction l E f).hom.app M) :=
    (pullReduction_existsUnique l E f).exists.choose_spec M
  have hpe := pullEvaluation_fac l E f n K
  have hpe' : (pullEvaluation l E f n).inv.app (DerivedCategory.Q.obj K) ≫
      (dev l E X n).map ((pull l E f).mapDerivedCategoryFactors.hom.app K) ≫
      (ev l E X n).mapDerivedCategoryFactors.hom.app (((pull l E f).mapHomologicalComplex
        (.up ℤ)).obj K) =
      (dpullModule l E f).map ((ev l E Y n).mapDerivedCategoryFactors.hom.app K) ≫
        (H l E f).mapDerivedCategoryFactors.hom.app
          (((ev l E Y n).mapHomologicalComplex (.up ℤ)).obj K) := by
    rw [← hpe, Iso.inv_hom_id_app_assoc]
  have hnat := (pullEvaluation l E f n).inv.naturality r
  have hev := (ev l E X n).mapDerivedCategoryFactors.hom.naturality
    ((strictPullReduction l E f).hom.app M)
  simp only [Functor.comp_obj, Functor.comp_map] at hnat hev
  rw [reassoc_of% hnat]
  have h2 := congrArg (dev l E X n).map hpr
  simp only [Functor.map_comp] at h2
  erw [reassoc_of% h2]
  erw [hev]
  rw [reassoc_of% hpe', ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

private theorem ψ_normalization (n : ℕ) (M : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    (dpullModule l E f).map (eI l E Y n M).inv ≫ (ψ l E f n).app (DerivedCategory.Q.obj M) ≫
        (C l E X n).map ((H l E f).mapDerivedCategoryFactors.hom.app M) ≫
        (eI l E X n (((H l E f).mapHomologicalComplex (.up ℤ)).obj M)).hom =
      (H l E f).mapDerivedCategoryFactors.hom.app ((Φ l E Y n).obj M) ≫
        DerivedCategory.Q.map ((s l E f n).app M) := by
  have h := ψ_normalization_aux l E f n M
  simp only [ψ, TwoSquare.hComp_app, C, Φ, eI, s, Iso.trans_inv, Iso.trans_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_inv, Iso.app_hom, Functor.comp_obj,
    Functor.comp_map, Functor.map_comp, Category.assoc]
  exact h

section Cone

variable {T : Scheme.{u}} {K L : CochainComplex (Tow l E T) ℤ} (φ₀ : K ⟶ L) (i : ℤ) (n : ℕ)

private theorem cone_id_app :
    ((CochainComplex.mappingCone.fst φ₀).1.v i (i + 1) rfl).app (op n) ≫
        ((CochainComplex.mappingCone.inl φ₀).v (i + 1) i (by omega)).app (op n) +
      ((CochainComplex.mappingCone.snd φ₀).v i i (add_zero i)).app (op n) ≫
        ((CochainComplex.mappingCone.inr φ₀).f i).app (op n) = 𝟙 _ := by
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← NatTrans.app_add,
    CochainComplex.mappingCone.id_X φ₀ i (i + 1) rfl]
  rfl

private theorem cone_inl_fst_app :
    ((CochainComplex.mappingCone.inl φ₀).v (i + 1) i (by omega)).app (op n) ≫
      ((CochainComplex.mappingCone.fst φ₀).1.v i (i + 1) rfl).app (op n) = 𝟙 _ := by
  rw [← NatTrans.comp_app, CochainComplex.mappingCone.inl_v_fst_v φ₀ (i + 1) i rfl]
  rfl

private theorem cone_inl_snd_app :
    ((CochainComplex.mappingCone.inl φ₀).v (i + 1) i (by omega)).app (op n) ≫
      ((CochainComplex.mappingCone.snd φ₀).v i i (add_zero i)).app (op n) = 0 := by
  rw [← NatTrans.comp_app, CochainComplex.mappingCone.inl_v_snd_v φ₀ (i + 1) i (by omega)]
  rfl

private theorem cone_inr_fst_app :
    ((CochainComplex.mappingCone.inr φ₀).f i).app (op n) ≫
      ((CochainComplex.mappingCone.fst φ₀).1.v i (i + 1) rfl).app (op n) = 0 := by
  rw [← NatTrans.comp_app, CochainComplex.mappingCone.inr_f_fst_v φ₀ i (i + 1) rfl]
  rfl

private theorem cone_inr_snd_app :
    ((CochainComplex.mappingCone.inr φ₀).f i).app (op n) ≫
      ((CochainComplex.mappingCone.snd φ₀).v i i (add_zero i)).app (op n) = 𝟙 _ := by
  rw [← NatTrans.comp_app, CochainComplex.mappingCone.inr_f_snd_v φ₀ i]
  rfl

end Cone

private theorem strictRed_inl {T : Scheme.{u}}
    {M N : CochainComplex (AdicCompletion.Modules l E T) ℤ}
    (g : M ⟶ N) (i : ℤ) :
    (CochainComplex.mappingCone.inl ((complexPowerMap l E T).app M)).v (i + 1) i (by omega) ≫
        ((strictRed l E T).map g).f i =
      (((scalarTower l E T).mapHomologicalComplex (.up ℤ)).map g).f (i + 1) ≫
        (CochainComplex.mappingCone.inl ((complexPowerMap l E T).app N)).v (i + 1) i
          (by omega) := by
  simp [strictRed, CochainComplex.mappingCone.map]

private theorem strictRed_inr {T : Scheme.{u}}
    {M N : CochainComplex (AdicCompletion.Modules l E T) ℤ}
    (g : M ⟶ N) (i : ℤ) :
    (CochainComplex.mappingCone.inr ((complexPowerMap l E T).app M)).f i ≫
        ((strictRed l E T).map g).f i =
      (((constant l E T).mapHomologicalComplex (.up ℤ)).map g).f i ≫
        (CochainComplex.mappingCone.inr ((complexPowerMap l E T).app N)).f i := by
  simp [strictRed, CochainComplex.mappingCone.map]

private theorem m_app (n : ℕ) (I : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    (m l E f n).app I = ((adj l E f).mapHomologicalComplex (.up ℤ)).unit.app
        ((Φ l E Y n).obj (((P l E f).mapHomologicalComplex (.up ℤ)).obj I)) ≫
      ((P l E f).mapHomologicalComplex (.up ℤ)).map
        ((s l E f n).app (((P l E f).mapHomologicalComplex (.up ℤ)).obj I) ≫
          (Φ l E X n).map (((adj l E f).mapHomologicalComplex (.up ℤ)).counit.app I)) := by
  have h := (((adj l E f).mapHomologicalComplex (.up ℤ)).homEquiv _ _).apply_symm_apply
    ((m l E f n).app I)
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_unit, m_counit] at h
  exact h.symm

private theorem unit_comp_map_eq {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {e x d : D} {b : C} (i₁ : G.obj e ⟶ b) (a : F.obj b ⟶ x) (c : x ⟶ d)
    (i₂ : e ⟶ d) (h : F.map i₁ ≫ a ≫ c = adj.counit.app e ≫ i₂) :
    i₁ ≫ adj.unit.app b ≫ G.map (a ≫ c) = G.map i₂ := by
  rw [← Category.assoc, ← adj.unit_naturality, Category.assoc, ← G.map_comp, h, G.map_comp,
    adj.right_triangle_components_assoc]

private theorem isIso_of_cone_components {C D : Type*} [Category C] [Preadditive C] [Category D]
    [Preadditive D] (G : C ⥤ D) [G.Additive] {a₁ a₂ Z : C} {A : D}
    (inl₁ : G.obj a₁ ⟶ A) (inr₁ : G.obj a₂ ⟶ A) (fst₁ : A ⟶ G.obj a₁) (snd₁ : A ⟶ G.obj a₂)
    (inl₂ : a₁ ⟶ Z) (inr₂ : a₂ ⟶ Z) (fst₂ : Z ⟶ a₁) (snd₂ : Z ⟶ a₂)
    (h₁ : fst₁ ≫ inl₁ + snd₁ ≫ inr₁ = 𝟙 A) (h₂ : fst₂ ≫ inl₂ + snd₂ ≫ inr₂ = 𝟙 Z)
    (h₃ : inl₂ ≫ fst₂ = 𝟙 _) (h₄ : inl₂ ≫ snd₂ = 0) (h₅ : inr₂ ≫ fst₂ = 0)
    (h₆ : inr₂ ≫ snd₂ = 𝟙 _) (m : A ⟶ G.obj Z) (hl : inl₁ ≫ m = G.map inl₂)
    (hr : inr₁ ≫ m = G.map inr₂) : IsIso m := by
  refine ⟨G.map fst₂ ≫ inl₁ + G.map snd₂ ≫ inr₁, ?_, ?_⟩
  · have hl' : G.map inl₂ ≫ (G.map fst₂ ≫ inl₁ + G.map snd₂ ≫ inr₁) = inl₁ := by
      simp [Preadditive.comp_add, ← G.map_comp_assoc, h₃, h₄]
    have hr' : G.map inr₂ ≫ (G.map fst₂ ≫ inl₁ + G.map snd₂ ≫ inr₁) = inr₁ := by
      simp [Preadditive.comp_add, ← G.map_comp_assoc, h₅, h₆]
    calc m ≫ (G.map fst₂ ≫ inl₁ + G.map snd₂ ≫ inr₁) =
        (fst₁ ≫ inl₁ + snd₁ ≫ inr₁) ≫ m ≫ (G.map fst₂ ≫ inl₁ + G.map snd₂ ≫ inr₁) := by
          rw [h₁, Category.id_comp]
      _ = fst₁ ≫ inl₁ + snd₁ ≫ inr₁ := by
          rw [Preadditive.add_comp, Category.assoc, Category.assoc, reassoc_of% hl,
            reassoc_of% hr, hl', hr']
      _ = 𝟙 A := h₁
  · rw [Preadditive.add_comp, Category.assoc, Category.assoc, hl, hr, ← G.map_comp, ← G.map_comp,
      ← G.map_add, h₂, G.map_id]

private theorem m_app_f (n : ℕ) (I : CochainComplex (AdicCompletion.Modules l E X) ℤ) (i : ℤ) :
    ((m l E f n).app I).f i = (adj l E f).unit.app
        ((((strictRed l E Y).obj (((P l E f).mapHomologicalComplex (.up ℤ)).obj I)).X i).obj
          (op n)) ≫
      (P l E f).map ((((strictPullReduction l E f).hom.app
          (((P l E f).mapHomologicalComplex (.up ℤ)).obj I)).f i).app (op n) ≫
        (((strictRed l E X).map (((adj l E f).mapHomologicalComplex (.up ℤ)).counit.app I)).f i).app
          (op n)) := by
  rw [m_app]
  rfl

private theorem m_inr (n : ℕ) (I : CochainComplex (AdicCompletion.Modules l E X) ℤ) (i : ℤ) :
    ((CochainComplex.mappingCone.inr ((complexPowerMap l E Y).app
        (((P l E f).mapHomologicalComplex (.up ℤ)).obj I))).f i).app (op n) ≫
      ((m l E f n).app I).f i =
      (P l E f).map (((CochainComplex.mappingCone.inr
        ((complexPowerMap l E X).app I)).f i).app (op n)) := by
  have hn := ((strictPullReduction_existsUnique l E f).exists.choose_spec
    (((P l E f).mapHomologicalComplex (.up ℤ)).obj I) i n).2
  have ha := congr_app (strictRed_inr l E
    (((adj l E f).mapHomologicalComplex (.up ℤ)).counit.app I) i) (op n)
  rw [m_app_f]
  exact unit_comp_map_eq (adj l E f) _ _ _ _ ((Category.assoc _ _ _).symm.trans
    ((hn =≫ _).trans ((NatTrans.comp_app _ _ _).symm.trans (ha.trans (NatTrans.comp_app _ _ _)))))

private theorem m_inl (n : ℕ) (I : CochainComplex (AdicCompletion.Modules l E X) ℤ) (i : ℤ) :
    ((CochainComplex.mappingCone.inl ((complexPowerMap l E Y).app
        (((P l E f).mapHomologicalComplex (.up ℤ)).obj I))).v (i + 1) i (by omega)).app (op n) ≫
      ((m l E f n).app I).f i =
      (P l E f).map (((CochainComplex.mappingCone.inl
        ((complexPowerMap l E X).app I)).v (i + 1) i (by omega)).app (op n)) := by
  have hn := ((strictPullReduction_existsUnique l E f).exists.choose_spec
    (((P l E f).mapHomologicalComplex (.up ℤ)).obj I) i n).1
  have ha := congr_app (strictRed_inl l E
    (((adj l E f).mapHomologicalComplex (.up ℤ)).counit.app I) i) (op n)
  rw [m_app_f]
  exact unit_comp_map_eq (adj l E f) _ _ _ _ ((Category.assoc _ _ _).symm.trans
    ((hn =≫ _).trans ((NatTrans.comp_app _ _ _).symm.trans (ha.trans (NatTrans.comp_app _ _ _)))))

private theorem m_isIso (n : ℕ) (I : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    IsIso ((m l E f n).app I) := by
  have (i : ℤ) : IsIso (((m l E f n).app I).f i) := by
    let φY := (complexPowerMap l E Y).app (((P l E f).mapHomologicalComplex (.up ℤ)).obj I)
    let φX := (complexPowerMap l E X).app I
    refine isIso_of_cone_components (P l E f) (a₁ := I.X (i + 1)) (a₂ := I.X i)
      (Z := ((CochainComplex.mappingCone φX).X i).obj (op n))
      (A := ((CochainComplex.mappingCone φY).X i).obj (op n))
      (((CochainComplex.mappingCone.inl φY).v (i + 1) i (by omega)).app (op n))
      (((CochainComplex.mappingCone.inr φY).f i).app (op n))
      (((CochainComplex.mappingCone.fst φY).1.v i (i + 1) rfl).app (op n))
      (((CochainComplex.mappingCone.snd φY).v i i (add_zero i)).app (op n))
      (((CochainComplex.mappingCone.inl φX).v (i + 1) i (by omega)).app (op n))
      (((CochainComplex.mappingCone.inr φX).f i).app (op n))
      (((CochainComplex.mappingCone.fst φX).1.v i (i + 1) rfl).app (op n))
      (((CochainComplex.mappingCone.snd φX).v i i (add_zero i)).app (op n))
      ?_ ?_ ?_ ?_ ?_ ?_ (((m l E f n).app I).f i) ?_ ?_
    · exact cone_id_app l E φY i n
    · exact cone_id_app l E φX i n
    · exact cone_inl_fst_app l E φX i n
    · exact cone_inl_snd_app l E φX i n
    · exact cone_inr_fst_app l E φX i n
    · exact cone_inr_snd_app l E φX i n
    · exact m_inl l E f n I i
    · exact m_inr l E f n I i
  exact HomologicalComplex.Hom.isIso_of_components _

private theorem coneKInjective {A : Type*} [Category A] [Abelian A] {K L : CochainComplex A ℤ}
    [K.IsKInjective] [L.IsKInjective] (g : K ⟶ L) :
    (CochainComplex.mappingCone g).IsKInjective := by
  rw [CochainComplex.isKInjective_iff_rightOrthogonal]
  refine ObjectProperty.ext_of_isTriangulatedClosed₃ _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished g) ?_ ?_
  · exact CochainComplex.IsKInjective.rightOrthogonal K
  · exact CochainComplex.IsKInjective.rightOrthogonal L

private theorem Φ_isKInjective (n : ℕ) (I : CochainComplex (AdicCompletion.Modules l E X) ℤ)
    [I.IsKInjective] : ((Φ l E X n).obj I).IsKInjective := by
  have : CochainComplex.IsKInjective (((ev l E X n).mapHomologicalComplex (.up ℤ)).obj
      (((scalarTower l E X).mapHomologicalComplex (.up ℤ)).obj I)) :=
    inferInstanceAs I.IsKInjective
  have : CochainComplex.IsKInjective (((ev l E X n).mapHomologicalComplex (.up ℤ)).obj
      (((constant l E X).mapHomologicalComplex (.up ℤ)).obj I)) :=
    inferInstanceAs I.IsKInjective
  have := coneKInjective (((ev l E X n).mapHomologicalComplex (.up ℤ)).map
    ((complexPowerMap l E X).app I))
  exact CochainComplex.isKInjective_of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso _ (ev l E X n)).symm

/-- The transpose of the left side of the normalization of `φ`. -/
private theorem φ_normalization_left (n : ℕ)
    (I : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    (dpullModule l E f).map ((eI l E Y n (((P l E f).mapHomologicalComplex (.up ℤ)).obj I)).inv ≫
        (C l E Y n).map (UnboundedExactTower.cochainUnit (P l E f) I) ≫
        (φ l E f n).app (DerivedCategory.Q.obj I) ≫
        (rpushModule l E f).map (eI l E X n I).hom) ≫
      (moduleAdjunction l E f).counit.app (DerivedCategory.Q.obj ((Φ l E X n).obj I)) =
    (H l E f).mapDerivedCategoryFactors.hom.app
        ((Φ l E Y n).obj (((P l E f).mapHomologicalComplex (.up ℤ)).obj I)) ≫
      DerivedCategory.Q.map ((s l E f n).app (((P l E f).mapHomologicalComplex (.up ℤ)).obj I)) ≫
      DerivedCategory.Q.map ((Φ l E X n).map
        (((adj l E f).mapHomologicalComplex (.up ℤ)).counit.app I)) := by
  simp only [Functor.map_comp, Category.assoc]
  erw [(moduleAdjunction l E f).counit_naturality]
  rw [reassoc_of% φ_counit, reassoc_of% ψ_naturality, ← Functor.map_comp_assoc, cochain_counit',
    Functor.map_comp_assoc,
    eI_naturality l E X n (M := ((H l E f).mapHomologicalComplex (.up ℤ)).obj
      (((P l E f).mapHomologicalComplex (.up ℤ)).obj I)) (N := I)]
  have h := ψ_normalization l E f n (((P l E f).mapHomologicalComplex (.up ℤ)).obj I) =≫
    DerivedCategory.Q.map ((Φ l E X n).map
      (((adj l E f).mapHomologicalComplex (.up ℤ)).counit.app I))
  simp only [Category.assoc] at h
  exact h

/-- The transpose of the right side of the normalization of `φ`. -/
private theorem φ_normalization_right (n : ℕ)
    (I : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    (dpullModule l E f).map (DerivedCategory.Q.map ((m l E f n).app I) ≫
        UnboundedExactTower.cochainUnit (P l E f) ((Φ l E X n).obj I)) ≫
      (moduleAdjunction l E f).counit.app (DerivedCategory.Q.obj ((Φ l E X n).obj I)) =
    (H l E f).mapDerivedCategoryFactors.hom.app
        ((Φ l E Y n).obj (((P l E f).mapHomologicalComplex (.up ℤ)).obj I)) ≫
      DerivedCategory.Q.map ((s l E f n).app (((P l E f).mapHomologicalComplex (.up ℤ)).obj I)) ≫
      DerivedCategory.Q.map ((Φ l E X n).map
        (((adj l E f).mapHomologicalComplex (.up ℤ)).counit.app I)) := by
  rw [Functor.map_comp, Category.assoc, cochain_counit']
  erw [(H l E f).mapDerivedCategoryFactors_hom_naturality_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, m_counit]
  rfl

private theorem φ_normalization (n : ℕ) (I : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    (eI l E Y n (((P l E f).mapHomologicalComplex (.up ℤ)).obj I)).inv ≫
        (C l E Y n).map (UnboundedExactTower.cochainUnit (P l E f) I) ≫
        (φ l E f n).app (DerivedCategory.Q.obj I) ≫
        (rpushModule l E f).map (eI l E X n I).hom =
      DerivedCategory.Q.map ((m l E f n).app I) ≫
        UnboundedExactTower.cochainUnit (P l E f) ((Φ l E X n).obj I) := by
  apply ((moduleAdjunction l E f).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  exact (φ_normalization_left l E f n I).trans (φ_normalization_right l E f n I).symm

private theorem φ_isIso (n : ℕ) : IsIso (φ l E f n) := by
  have hI (I : CochainComplex (AdicCompletion.Modules l E X) ℤ) (_ : I.IsKInjective) :
      IsIso ((φ l E f n).app (DerivedCategory.Q.obj I)) := by
    have : IsIso (UnboundedExactTower.cochainUnit (P l E f) I) := by
      unfold UnboundedExactTower.cochainUnit
      infer_instance
    have := Φ_isKInjective l E n I
    have : IsIso (UnboundedExactTower.cochainUnit (P l E f) ((Φ l E X n).obj I)) := by
      unfold UnboundedExactTower.cochainUnit
      infer_instance
    have := m_isIso l E f n I
    have h := φ_normalization l E f n I
    have : IsIso ((eI l E Y n (((P l E f).mapHomologicalComplex (.up ℤ)).obj I)).inv ≫
        (C l E Y n).map (UnboundedExactTower.cochainUnit (P l E f) I) ≫
        (φ l E f n).app (DerivedCategory.Q.obj I) ≫
        (rpushModule l E f).map (eI l E X n I).hom) := by
      rw [h]
      infer_instance
    simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using this
  have hK (K : DerivedCategory (AdicCompletion.Modules l E X)) : IsIso ((φ l E f n).app K) := by
    obtain ⟨I, hIi, ⟨eI⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
    have := hI I hIi
    have hs : IsIso ((rpushModule l E f ⋙ C l E Y n).map eI.hom ≫
        (φ l E f n).app (DerivedCategory.Q.obj I)) := inferInstance
    rw [(φ l E f n).naturality eI.hom] at hs
    exact IsIso.of_isIso_comp_right ((φ l E f n).app K)
      ((C l E X n ⋙ rpushModule l E f).map eI.hom)
  exact NatIso.isIso_of_isIso_app _

end LevelwiseIso

open LevelwiseIso in
/-- Every finite reduction evaluation of the direct-image reduction mate is an isomorphism. -/
theorem directImage_pushReductionMap_levelwiseIso :
    ∀ K : DerivedCategory (AdicCompletion.Modules l E X), ∀ n : ℕ,
      IsIso ((CompleteDerivedCompletion.dev l E Y n).map
        (((mateEquiv (moduleAdjunction l E f) (towerAdjunction l E f)
          (.mk _ _ _ _ (pullReduction l E f).hom))).app K)) := by
  intro K n
  have hv := mateEquiv_vcomp (moduleAdjunction l E f) (towerAdjunction l E f)
    (moduleAdjunction l E f) (.mk _ _ _ _ (pullReduction l E f).hom)
    (.mk _ _ _ _ (pullEvaluation l E f n).inv)
  have hK := congr_app hv K
  have := φ_isIso l E f n
  have hφ : IsIso ((φ l E f n).app K) := inferInstance
  obtain ⟨β, hβ, -⟩ := (completeDerivedCompletion l E Y X f).2.2.2.1.2.2.2
  have : IsIso ((pushEvaluationMap l E f n).app ((red l E X).obj K)) := by
    rw [← hβ n]
    infer_instance
  have hφ' : IsIso ((mateEquiv (moduleAdjunction l E f) (moduleAdjunction l E f)
      ((TwoSquare.mk _ _ _ _ (pullReduction l E f).hom).hComp
        (TwoSquare.mk _ _ _ _ (pullEvaluation l E f n).inv))).app K) := hφ
  rw [hK] at hφ'
  simp only [TwoSquare.vComp_app, Functor.comp_obj] at hφ'
  change IsIso (_ ≫ (pushEvaluationMap l E f n).app _) at hφ'
  exact IsIso.of_isIso_comp_right _ ((pushEvaluationMap l E f n).app ((red l E X).obj K))

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
