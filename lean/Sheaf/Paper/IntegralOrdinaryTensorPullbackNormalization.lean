/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V6
-/
module

public import Sheaf.Paper.SixFunctorOperationDatumStages
public import Sheaf.Paper.IntegralCompactSupportCoefficientData
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import Sheaf.Paper.IntegralTensorPullbackAugmentation
import Sheaf.Paper.ConstructibleTensorCompletionComparison
import Sheaf.Paper.ConstructibleTensorCompletionConstructible
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

/-- On the constructible domain, ordinary signed K-flat tensor models identify
completed tensor and pullback with their ordinary counterparts, compatibly with
the specified tensor-pullback comparison. No direct image, adjunction counit,
projection morphism, or projection invertibility occurs in this assertion.

Source: fix-prop-projection-formula.proof.md, integral reconstruction;
Bhatt--Scholze, Lemma 6.5.5 and Proposition 6.6.11; Stacks, Tags 07A4 and 0941.
(blueprint: lem-sf-integral-ordinary-tensor-pullback-normalization).

Proof: choose the signed total tensor models over the completed coefficient
sheaves. The quotient-map tensor completion comparison is invertible on each
constructible pair. Restrict its inverse to the full constructible categories;
naturality gives the tensor comparisons m and n. Ordinary completed pullback
comparison is likewise invertible on each constructible input. Its natural
restriction, with the datum's pullback equality, gives a. The tensor and pullback
normalizations of H identify the supplied component with the canonical coherent
quotient-system component. Compare the two routes in the displayed tensor square
on simultaneous flat-term K-flat representatives. In every positive quotient,
both take a tensor of sections to the tensor of their pullbacks; the transition
maps are the same quotient maps. Their maps to the strict Roos cones have these
quotient components and zero shifted component. The representative comparison
squares therefore agree before localization. Descend along the product K-flat
localization and insert the inverse constructible completion units to obtain
ComparisonCompatible. Finite type over the given field supplies qcqs,
Noetherianness, finite dimension and invertibility of the coefficient prime.
The same comparisons apply to zero objects and empty schemes. -/
theorem integralOrdinaryTensorPullbackNormalization
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (H : SixFunctorHigherOperations D C E) (Q : SixFunctorCompactifiedSquare D) :
    ∃ (aZ : ProEtaleTensorModel Q.Z.obj.left
        ((PurCompactSupport.completed C.l E).ring Q.Z.obj.left))
      (aY : ProEtaleTensorModel Q.Y.obj.left
        ((PurCompactSupport.completed C.l E).ring Q.Y.obj.left))
      (a : (sfIntegralConstructible C.l E Q.Y.obj.left).ι ⋙
          PurCompactSupport.pull (PurCompactSupport.completed C.l E) Q.p.hom.left ≅
        (H.integralExchange Q).stage.properPull ⋙
          (sfIntegralConstructible C.l E Q.Z.obj.left).ι)
      (m : (Functor.postcompose₂.obj (sfIntegralConstructible C.l E Q.Z.obj.left).ι).obj
          (H.integralExchange Q).stage.tensorBar ≅
        (((Functor.whiskeringLeft₂ _).obj
          (sfIntegralConstructible C.l E Q.Z.obj.left).ι).obj
            (sfIntegralConstructible C.l E Q.Z.obj.left).ι).obj
              (Functor.curry.obj aZ.tensor))
      (n : (Functor.postcompose₂.obj (sfIntegralConstructible C.l E Q.Y.obj.left).ι).obj
          (H.integralExchange Q).stage.tensorY ≅
        (((Functor.whiskeringLeft₂ _).obj
          (sfIntegralConstructible C.l E Q.Y.obj.left).ι).obj
            (sfIntegralConstructible C.l E Q.Y.obj.left).ι).obj
              (Functor.curry.obj aY.tensor)),
      Adjunction.ComparisonCompatible a (H.integralExchange Q).stage.tensorPullback.hom
        (ordinaryCurriedTensorPullback (PurCompactSupport.completed C.l E)
          Q.p.hom.left aZ aY).hom m n := by
  classical
  have hcompact (X : SixFunctorSpace D) : CompactSpace X.obj.left :=
    QuasiCompact.compactSpace_of_compactSpace (X.obj.left ↘ Spec (.of D.k))
  have hlocal (X : SixFunctorSpace D) : IsLocallyNoetherian X.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian (X.obj.left ↘ Spec (.of D.k))
  have hnoeth (X : SixFunctorSpace D) : IsNoetherian X.obj.left := by
    have := hcompact X
    have := hlocal X
    exact ⟨⟩
  let (X : SixFunctorSpace D) : IsNoetherian X.obj.left := hnoeth X
  have hunit (X : SixFunctorSpace D) : IsUnit (C.l : Γ(X.obj.left, ⊤)) := by
    let ρ := (Scheme.ΓSpecIso (.of D.k)).inv ≫ (X.obj.left ↘ Spec (.of D.k)).appTop
    simpa only [map_natCast] using
      (PurCompactSupport.coefficientPrimeUnit C.l D C.different).map ρ.hom
  let (X : SixFunctorSpace D) (x : X.obj.left) :
      Invertible (C.l : X.obj.left.residueField x) := by
    have hs : IsUnit (C.l : X.obj.left.presheaf.stalk x) := by
      simpa only [map_natCast] using
        (hunit X).map (X.obj.left.presheaf.germ ⊤ x trivial).hom
    have hr : IsUnit (C.l : X.obj.left.residueField x) := by
      simpa only [map_natCast] using hs.map (X.obj.left.residue x).hom
    exact hr.invertible
  have hdim (X : SixFunctorSpace D) : ∃ n : ℕ, topologicalKrullDim X.obj.left ≤ n := by
    have hd := topologicalKrullDim_lt_top_of_finiteType (X.obj.left ↘ Spec (.of D.k))
    obtain h | h := eq_or_ne (topologicalKrullDim X.obj.left) ⊥
    · exact ⟨0, by simp only [h, bot_le]⟩
    · obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp h
      rw [← ha] at hd ⊢
      change (a : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) at hd
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (WithBot.coe_lt_coe.mp hd).ne
      exact ⟨n, by rw [← hn]; exact le_rfl⟩
  refine ⟨IntegralOrdinary.tensorModel C.l E Q.Z.obj.left,
    IntegralOrdinary.tensorModel C.l E Q.Y.obj.left, ?_⟩
  exact canonicalCoordinates C.l E Q.p.hom.left (hdim Q.Z) (hdim Q.Y)
    (hunit Q.Z) (hunit Q.Y) _ _ _ (H.integralExchange Q).stage.tensorPullback
    ((H.integralExchange Q).properPull.trans (H.integralPullback Q.p))
    ((H.integralExchange Q).tensorBar.trans (H.integralTensorNormalization Q.Z))
    ((H.integralExchange Q).tensorY.trans (H.integralTensorNormalization Q.Y))
    (H.integralTensorPullbackNormalization Q)

end WeilConjectures
