/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.SixFunctorOperationDatumStages
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralTensorPullbackAugmentation
import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionComparison
import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionConstructible
import WeilConjectures.AlgebraicGeometry.DimensionFiniteTypeField

/-! # Ordinary coordinates for integral tensor and pullback

Source: the integral reconstruction in fix-prop-projection-formula.proof.md,
using constructible tensor completion and ordinary/completed integral pullback.
This statement concerns only left operation functors and their tensor comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] proEtaleCanonicalTensorComparison

/-- The componentwise currying of the canonical ordinary tensor-pullback isomorphism.
Source: Stacks Tag 07A4
(blueprint: lem-sf-integral-ordinary-tensor-pullback-normalization). -/
def ordinaryCurriedTensorPullback (R : PurCompactSupport.Coefficients.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aX : ProEtaleTensorModel X (R.ring X))
    (aY : ProEtaleTensorModel Y (R.ring Y)) :
    (Functor.postcompose₂.obj (PurCompactSupport.pull R f)).obj
        (PurCompactSupport.tensorCurried aY) ≅
      (((Functor.whiskeringLeft₂ _).obj (PurCompactSupport.pull R f)).obj
        (PurCompactSupport.pull R f)).obj (PurCompactSupport.tensorCurried aX) :=
  let tau := proEtaleCanonicalTensorComparison f (R.ring Y) (R.ring X) (R.pull f) aY aX
  NatIso.ofComponents
    (fun M ↦ NatIso.ofComponents (fun N ↦ tau.app (M, N)) (by
      intro N N' h
      simpa using tau.hom.naturality (Prod.mkHom (𝟙 M) h))) (by
      intro M M' h
      ext N
      simpa using tau.hom.naturality (Prod.mkHom h (𝟙 N)))

private theorem tensorAugmentation (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [∀ x : X, Invertible (l : X.residueField x)] :
    ∃ τ : (IntegralOrdinary.tensorModel l E X).tensor ⟶ integralCompletedTensor l E X,
      IntegralOrdinary.TensorAugmentationNormalized l E X τ ∧
      ∀ M N : sfIntegralConstructibleCategory l E X, IsIso (τ.app (M.obj, N.obj)) := by
  obtain ⟨τ, hτ, hτiso⟩ := ConstructibleTensorModel.tensorCompletionComparison l E X
  refine ⟨τ, hτ, fun M N ↦ ?_⟩
  exact hτiso M.obj N.obj
    (ConstructibleTensorModel.tensorComplete_onConstructible l E X M.obj N.obj
      M.property N.property).2

private def tensorCoordinates (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)]
    (τ : (IntegralOrdinary.tensorModel l E X).tensor ⟶ integralCompletedTensor l E X)
    (hτ : ∀ M N : sfIntegralConstructibleCategory l E X,
      IsIso (τ.app (M.obj, N.obj))) :
    (Functor.postcompose₂.obj (sfIntegralConstructible l E X).ι).obj
        (Functor.currying.inverse.obj (constructibleIntegralTensor l E X)) ≅
      (((Functor.whiskeringLeft₂ _).obj (sfIntegralConstructible l E X).ι).obj
        (sfIntegralConstructible l E X).ι).obj
          (Functor.curry.obj (IntegralOrdinary.tensorModel l E X).tensor) := by
  refine (NatIso.ofComponents (fun M ↦ NatIso.ofComponents
    (fun N ↦ @asIso _ _ _ _ (τ.app (M.obj, N.obj)) (hτ M N)) ?_) ?_).symm
  · intro N N' h
    exact τ.naturality (Prod.mkHom (𝟙 M.obj) h.hom)
  · intro M M' h
    ext N
    exact τ.naturality (Prod.mkHom h.hom (𝟙 N.obj))

private theorem canonicalCoordinates (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hXdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (hYdim : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
    (hXinv : IsUnit (l : Γ(X, ⊤))) (hYinv : IsUnit (l : Γ(Y, ⊤)))
    (F : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E X)
    (TX : sfIntegralConstructibleCategory l E X ⥤
      sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E X)
    (TY : sfIntegralConstructibleCategory l E Y ⥤
      sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E Y)
    (φ : (Functor.postcompose₂.obj F).obj TY ≅
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj TX)
    (hF : F = constructibleIntegralPullback l E f)
    (hTX : TX = Functor.currying.inverse.obj (constructibleIntegralTensor l E X))
    (hTY : TY = Functor.currying.inverse.obj (constructibleIntegralTensor l E Y))
    (hφ : ∀ M N : sfIntegralConstructibleCategory l E Y,
      HEq ((φ.hom.app M).app N) (canonicalIntegralPullbackTensor l E f M N).hom) :
    ∃ (a : (sfIntegralConstructible l E Y).ι ⋙
          PurCompactSupport.pull (PurCompactSupport.completed l E) f ≅
        F ⋙ (sfIntegralConstructible l E X).ι)
      (m : (Functor.postcompose₂.obj (sfIntegralConstructible l E X).ι).obj TX ≅
        (((Functor.whiskeringLeft₂ _).obj (sfIntegralConstructible l E X).ι).obj
          (sfIntegralConstructible l E X).ι).obj
            (Functor.curry.obj (IntegralOrdinary.tensorModel l E X).tensor))
      (n : (Functor.postcompose₂.obj (sfIntegralConstructible l E Y).ι).obj TY ≅
        (((Functor.whiskeringLeft₂ _).obj (sfIntegralConstructible l E Y).ι).obj
          (sfIntegralConstructible l E Y).ι).obj
            (Functor.curry.obj (IntegralOrdinary.tensorModel l E Y).tensor)),
      Adjunction.ComparisonCompatible a φ.hom
        (ordinaryCurriedTensorPullback (PurCompactSupport.completed l E) f
          (IntegralOrdinary.tensorModel l E X) (IntegralOrdinary.tensorModel l E Y)).hom m n := by
  subst F TX TY
  obtain ⟨τX, hτX, hiX⟩ := tensorAugmentation l E X
  obtain ⟨τY, hτY, hiY⟩ := tensorAugmentation l E Y
  let a : (sfIntegralConstructible l E Y).ι ⋙
      PurCompactSupport.pull (PurCompactSupport.completed l E) f ≅
      constructibleIntegralPullback l E f ⋙ (sfIntegralConstructible l E X).ι :=
    NatIso.ofComponents (fun M ↦ @asIso _ _ _ _
      ((IntegralOrdinary.pullComparison l E f).app M.obj)
        (IntegralOrdinary.pullComparison_isIso l E f hXdim hYdim hXinv hYinv M))
      (fun h ↦ (IntegralOrdinary.pullComparison l E f).naturality h.hom)
  refine ⟨a, tensorCoordinates l E X τX hiX, tensorCoordinates l E Y τY hiY, ?_⟩
  intro M N
  let O := PurCompactSupport.pull (PurCompactSupport.completed l E) f
  let R := IntegralOrdinary.pullComparison l E f
  let t := (IntegralOrdinary.tensorModel l E X).tensor
  let v := (proEtaleCanonicalTensorComparison f
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f)
    (IntegralOrdinary.tensorModel l E Y) (IntegralOrdinary.tensorModel l E X)).hom.app
      (M.obj, N.obj)
  have hR (K : sfIntegralConstructibleCategory l E Y) : IsIso (R.app K.obj) :=
    IntegralOrdinary.pullComparison_isIso l E f hXdim hYdim hXinv hYinv K
  have : IsIso (R.app ((integralCompletedTensor l E Y).obj (M.obj, N.obj))) :=
    hR ((constructibleIntegralTensor l E Y).obj (M, N))
  have := hiY M N
  have : IsIso (τX.app ((integralDerivedPullback l E f).obj M.obj,
      (integralDerivedPullback l E f).obj N.obj)) :=
    hiX ((constructibleIntegralPullback l E f).obj M)
      ((constructibleIntegralPullback l E f).obj N)
  have hmap := congrArg (fun z ↦ (sfIntegralConstructible l E X).ι.map z)
    (eq_of_heq (hφ M N))
  change (sfIntegralConstructible l E X).ι.map ((φ.hom.app M).app N) ≫
      inv (τX.app ((integralDerivedPullback l E f).obj M.obj,
        (integralDerivedPullback l E f).obj N.obj)) =
    inv (R.app ((integralCompletedTensor l E Y).obj (M.obj, N.obj))) ≫
      O.map (inv (τY.app (M.obj, N.obj))) ≫ v ≫
      t.map (Prod.mkHom (R.app M.obj) (𝟙 _)) ≫
      t.map (Prod.mkHom (𝟙 _) (R.app N.obj))
  rw [hmap]
  have haug := IntegralOrdinary.tensorPullback_augmentation l E f τX τY hτX hτY M N
  have hnat := τX.naturality (Prod.mkHom (R.app M.obj) (R.app N.obj))
  have hfwd : O.map (τY.app (M.obj, N.obj)) ≫
      R.app ((integralCompletedTensor l E Y).obj (M.obj, N.obj)) ≫
      ((canonicalIntegralPullbackTensor l E f M N).hom).hom =
    v ≫ t.map (Prod.mkHom (R.app M.obj) (R.app N.obj)) ≫
      τX.app ((integralDerivedPullback l E f).obj M.obj,
        (integralDerivedPullback l E f).obj N.obj) := by
    exact haug.trans (by rw [← hnat])
  have htmap : t.map (Prod.mkHom (R.app M.obj) (𝟙 _)) ≫
      t.map (Prod.mkHom (𝟙 _) (R.app N.obj)) =
    t.map (Prod.mkHom (R.app M.obj) (R.app N.obj)) := by
    rw [← t.map_comp]
    simp
  rw [htmap]
  apply (cancel_epi (R.app ((integralCompletedTensor l E Y).obj (M.obj, N.obj)))).1
  apply (cancel_epi (O.map (τY.app (M.obj, N.obj)))).1
  apply (cancel_mono (τX.app ((integralDerivedPullback l E f).obj M.obj,
    (integralDerivedPullback l E f).obj N.obj))).1
  simp only [Category.assoc, Functor.map_inv, IsIso.hom_inv_id_assoc,
    IsIso.inv_hom_id, Category.comp_id, ObjectProperty.ι_map]
  exact hfwd

end WeilConjectures
