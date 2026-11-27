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
private abbrev C (T : Scheme.{u}) (n : ℕ) := red l E T ⋙ dev l E T n

/-- The strict model of the finite reduction functor at level `n`. -/
private abbrev Φ (T : Scheme.{u}) (n : ℕ) :
    CochainComplex (AdicCompletion.Modules l E T) ℤ ⥤ CochainComplex (AdicCompletion.Modules l E T) ℤ :=
  strictRed l E T ⋙ (ev l E T n).mapHomologicalComplex (.up ℤ)

/-- The finite reduction functor computed on the strict model. -/
private def e (T : Scheme.{u}) (n : ℕ) :
    DerivedCategory.Q ⋙ C l E T n ≅ Φ l E T n ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (redFactors l E T) (dev l E T n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (strictRed l E T) (ev l E T n).mapDerivedCategoryFactors

private theorem e_hom_app (T : Scheme.{u}) (n : ℕ)
    (M : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    (e l E T n).hom.app M = (dev l E T n).map ((redFactors l E T).hom.app M) ≫
      (ev l E T n).mapDerivedCategoryFactors.hom.app ((strictRed l E T).obj M) := by
  simp [e]

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
private def ψ (n : ℕ) : TwoSquare (C l E Y n) (dpullModule l E f) (dpullModule l E f) (C l E X n) :=
  TwoSquare.mk _ _ _ _ (pullReduction l E f).hom ≫ₕ
    TwoSquare.mk _ _ _ _ (pullEvaluation l E f n).inv

/-- The module-level mate of `ψ`. -/
private def φ (n : ℕ) :=
  mateEquiv (moduleAdjunction l E f) (moduleAdjunction l E f) (ψ l E f n)

/-- The ordinary mate of the strict comparison. -/
private def m (n : ℕ) :=
  mateEquiv ((adj l E f).mapHomologicalComplex (.up ℤ)) ((adj l E f).mapHomologicalComplex (.up ℤ))
    (TwoSquare.mk _ _ _ _ (s l E f n))

private theorem ψ_normalization (n : ℕ) (M : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    (dpullModule l E f).map ((e l E Y n).inv.app M) ≫ (ψ l E f n).app (DerivedCategory.Q.obj M) ≫
        (C l E X n).map ((H l E f).mapDerivedCategoryFactors.hom.app M) ≫
        (e l E X n).hom.app (((H l E f).mapHomologicalComplex (.up ℤ)).obj M) =
      (H l E f).mapDerivedCategoryFactors.hom.app ((Φ l E Y n).obj M) ≫
        DerivedCategory.Q.map ((s l E f n).app M) := by
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
  have hinv : (e l E Y n).inv.app M = (ev l E Y n).mapDerivedCategoryFactors.inv.app K ≫
      (dev l E Y n).map r := by
    rw [← cancel_epi ((e l E Y n).hom.app M), Iso.hom_inv_id_app, e_hom_app, Category.assoc,
      Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    rfl
  simp only [Functor.comp_obj, Functor.comp_map] at hnat hev
  simp only [ψ, TwoSquare.hComp_app, hinv, e_hom_app, Functor.map_comp, Category.assoc,
    Functor.comp_map]
  rw [reassoc_of% hnat]
  have h2 := congrArg (dev l E X n).map hpr
  simp only [Functor.map_comp] at h2
  erw [reassoc_of% h2]
  erw [hev]
  rw [reassoc_of% hpe', ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

private theorem m_isIso (n : ℕ) (I : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    IsIso ((m l E f n).app I) := by
  sorry

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

private theorem φ_normalization (n : ℕ) (I : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    (e l E Y n).inv.app (((P l E f).mapHomologicalComplex (.up ℤ)).obj I) ≫
        (C l E Y n).map (UnboundedExactTower.cochainUnit (P l E f) I) ≫
        (φ l E f n).app (DerivedCategory.Q.obj I) ≫
        (rpushModule l E f).map ((e l E X n).hom.app I) =
      DerivedCategory.Q.map ((m l E f n).app I) ≫
        UnboundedExactTower.cochainUnit (P l E f) ((Φ l E X n).obj I) := by
  sorry

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
    have : IsIso ((e l E Y n).inv.app (((P l E f).mapHomologicalComplex (.up ℤ)).obj I) ≫
        (C l E Y n).map (UnboundedExactTower.cochainUnit (P l E f) I) ≫
        (φ l E f n).app (DerivedCategory.Q.obj I) ≫
        (rpushModule l E f).map ((e l E X n).hom.app I)) := by
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
  change IsIso ((mateEquiv (moduleAdjunction l E f) (moduleAdjunction l E f)
    (ψ l E f n)).app K) at hφ
  rw [ψ, hK] at hφ
  simp only [TwoSquare.vComp_app, Functor.comp_obj] at hφ
  change IsIso (_ ≫ (pushEvaluationMap l E f n).app _) at hφ
  exact IsIso.of_isIso_comp_right _ ((pushEvaluationMap l E f n).app ((red l E X).obj K))

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
