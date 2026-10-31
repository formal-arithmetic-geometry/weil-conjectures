/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalScalarCompletionUnitSquare
public import WeilConjectures.AlgebraicGeometry.Rational.RationalPullbackCompositionCoherence
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarOperationComp

/-! # Integral mixed geometric composition by cancellation of completion units -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp

variable (l : ℕ) [Fact l.Prime]
variable (E F : Type u) [Field E] [Field F]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
variable (i : E →ₐ[ℚ_[l]] F)
variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

variable (g : X ⟶ Y)
  (sXE : RationalModuleRealization l E X) (sYE : RationalModuleRealization l E Y)
  (sXF : RationalModuleRealization l F X) (sYF : RationalModuleRealization l F Y)
  (aE : RationalRealizationPullbackComparison l E g sXE sYE)
  (aF : RationalRealizationPullbackComparison l F g sXF sYF)

variable {Z : Scheme.{u}} [IsNoetherian Z]
  [Fact (∃ n : ℕ, topologicalKrullDim Z ≤ n)]
  [Fact (∀ z : Z, IsUnit (l : Z.presheaf.stalk z))]
variable (h : Z ⟶ X) (sZE : RationalModuleRealization l E Z)
  (sZF : RationalModuleRealization l F Z)
  (ahE : RationalRealizationPullbackComparison l E h sZE sXE)
  (acE : RationalRealizationPullbackComparison l E (h ≫ g) sZE sYE)
  (ahF : RationalRealizationPullbackComparison l F h sZF sXF)
  (acF : RationalRealizationPullbackComparison l F (h ≫ g) sZF sYF)

private theorem mixed_localization_obj
    {R A : Type*} [CommRing R] [Category A] [Preadditive A] [Linear R A]
    (p : R) (K : A) : ((ScalarLocalization.localization R A p).obj K).obj = K := rfl

private theorem mixed_map_three {A B : Type*} [Category A] [Category B]
    (T : A ⥤ B) {U V W Z P : A} {a : U ⟶ V} {b : V ⟶ W} {c : W ⟶ Z}
    {d : U ⟶ P} {e : P ⟶ Z} (h : a ≫ b ≫ c = d ≫ e) :
    T.map a ≫ T.map b ≫ T.map c = T.map d ≫ T.map e := by
  simpa only [Functor.map_comp] using congrArg T.map h

private theorem mixed_map_two {A B : Type*} [Category A] [Category B]
    (T : A ⥤ B) {U V Z P : A} {a : U ⟶ V} {b : V ⟶ Z}
    {d : U ⟶ P} {e : P ⟶ Z} (h : a ≫ b = d ≫ e) :
    T.map a ≫ T.map b = T.map d ≫ T.map e := by
  simpa only [Functor.map_comp] using congrArg T.map h

private theorem mixed_cancel_pasting {D : Type*} [Category D]
    {A B C E F G H I J K L M Z : D}
    (u : A ⟶ B) (v : B ⟶ C) [Epi u] [Epi v]
    (c : C ⟶ E) (βc : E ⟶ Z) (βh : C ⟶ F) (f : F ⟶ G) (k : G ⟶ Z)
    (d : A ⟶ H) (e : H ⟶ E) (b : H ⟶ I) (γ : I ⟶ Z)
    (o : B ⟶ J) (η : J ⟶ F) (p : A ⟶ K) (a : K ⟶ J)
    (q : J ⟶ L) (θ : L ⟶ G) (r : K ⟶ M) (s : M ⟶ L) (t : M ⟶ I)
    (z : I ⟶ M) (hz : z ≫ t = 𝟙 I)
    (hE : u ≫ v ≫ c = d ≫ e) (hc : e ≫ βc = b ≫ γ)
    (hh : v ≫ βh = o ≫ η) (hn : u ≫ o = p ≫ a)
    (hu : η ≫ f = q ≫ θ) (hg : a ≫ q = r ≫ s)
    (hF : s ≫ θ ≫ k = t ≫ γ) (ho : p ≫ r = d ≫ b ≫ z) :
    c ≫ βc = βh ≫ f ≫ k := by
  apply (cancel_epi v).1
  apply (cancel_epi u).1
  calc
    u ≫ v ≫ c ≫ βc = d ≫ b ≫ γ := by
      rw [reassoc_of% hE, hc]
    _ = p ≫ r ≫ t ≫ γ := by rw [reassoc_of% ho, reassoc_of% hz]
    _ = p ≫ r ≫ s ≫ θ ≫ k := by rw [hF]
    _ = p ≫ a ≫ q ≫ θ ≫ k := by rw [reassoc_of% hg]
    _ = u ≫ o ≫ η ≫ f ≫ k := by rw [reassoc_of% hu, reassoc_of% hn]
    _ = u ≫ v ≫ βh ≫ f ≫ k := by rw [reassoc_of% hh]

private theorem mixed_raw_pasting
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (L : A ⥤ C) (M : B ⥤ D) (S : A ⥤ B) (T : C ⥤ D)
    (β : L ⋙ T ≅ S ⋙ M)
    {A₀ A₁ : A} {P₀ P₁ : B} {C₀ C₁ C₂ : C} {D₀ D₁ D₂ D₃ : D}
    (eg : A₀ ≅ A₁) (ef : P₀ ≅ P₁) (eh : L.obj A₁ ≅ C₀) (ec : C₂ ≅ C₁)
    (uh : M.obj (S.obj A₁) ≅ D₀) (vh : M.obj P₁ ≅ D₁) (uc : D₃ ≅ D₂)
    (r : C₀ ⟶ C₁) (q : S.obj A₁ ⟶ P₁) (f : D₀ ⟶ D₁) (c : D₁ ⟶ D₂)
    (x : T.obj C₁ ⟶ D₂) (y : T.obj C₀ ⟶ D₀)
    (cr : L.obj A₀ ⟶ C₂) (cf : M.obj P₀ ⟶ D₃)
    (bg : S.obj A₀ ⟶ P₀) (bc : T.obj C₂ ⟶ D₃)
    (hr : cr = L.map eg.hom ≫ eh.hom ≫ r ≫ ec.inv)
    (hf : cf = M.map ef.hom ≫ vh.hom ≫ c ≫ uc.inv)
    (hg : bg = S.map eg.hom ≫ q ≫ ef.inv)
    (hc : bc = T.map ec.hom ≫ x ≫ uc.inv)
    (hh : β.hom.app A₁ = T.map eh.hom ≫ y ≫ uh.inv)
    (hq : M.map q = uh.hom ≫ f ≫ vh.inv)
    (h : T.map r ≫ x = y ≫ f ≫ c) :
    T.map cr ≫ bc = β.hom.app A₀ ≫ M.map bg ≫ cf := by
  have hn := β.hom.naturality eg.hom
  simp only [Functor.comp_map] at hn
  simp only [hr, hf, hg, hc, Functor.map_comp, Category.assoc]
  rw [ef.map_inv_hom_id_assoc M]
  rw [← reassoc_of% hn, hh, hq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [ec.map_inv_hom_id_assoc T]
  rw [reassoc_of% h]

/-- Scalar extension commutes with the selected integral geometric compositors.
Source: BS Remark 6.8.15; Stacks 0D6D, 099N.
(blueprint: lem-per-mixed-integral-geometric-composition).

Proof: invert the ordinary scalar-pullback composition equation. Precompose by
scalar extension of the pullback of the first completion unit and then the
second unit. Naturality and the strict-beta unit squares reduce both routes to
the ordinary equation followed by the composite completion unit. The supplied
integral compositor unit equations identify the outer maps. Both precomposing
units are invertible on the constructible objects, so cancel them. -/
theorem rationalMixedIntegralGeometricComposition
    (cE : aE.integral.completedFunctor l E ⋙ ahE.integral.completedFunctor l E ≅
      acE.integral.completedFunctor l E)
    (cF : aF.integral.completedFunctor l F ⋙ ahF.integral.completedFunctor l F ≅
      acF.integral.completedFunctor l F)
    (uE : ∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E),
      (pbcActualDerivedPull h (pbcIntegralDatum l E)).map
          ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj) ≫
        (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app
          ((aE.integral.completedFunctor l E).obj K).obj ≫ (cE.hom.app K).hom =
      (pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)).inv.app K.obj ≫
        (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) (h ≫ g)).app K.obj)
    (uF : ∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l F),
      (pbcActualDerivedPull h (pbcIntegralDatum l F)).map
          ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l F) g).app K.obj) ≫
        (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l F) h).app
          ((aF.integral.completedFunctor l F).obj K).obj ≫ (cF.hom.app K).hom =
      (pbcActualDerivedPullCompIso h g (pbcIntegralDatum l F)).inv.app K.obj ≫
        (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l F) (h ≫ g)).app K.obj)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l E F i Z).map (cE.hom.app K).hom ≫
        (rationalScalarStrictBeta l E F i (h ≫ g)).hom.app K.obj =
      (rationalScalarStrictBeta l E F i h).hom.app
          ((aE.integral.completedFunctor l E).obj K).obj ≫
        (pbcActualStrictCompletedPull (pbcIntegralDatum l F) h).map
          ((rationalScalarStrictBeta l E F i g).hom.app K.obj) ≫
        (cF.hom.app ((pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K)).hom := by
  let C := pbcEmbeddingAmbientTensor l E F i Z
  let H := pbcActualDerivedPull h (pbcIntegralDatum l F)
  let T := (pbcEmbeddingIntegralTensor l E F i Y Fact.out Fact.out).obj K
  have ug : IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app
      K.obj) := aE.integral.unit_isIso K
  have uh : IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app
      ((aE.integral.completedFunctor l E).obj K).obj) :=
    ahE.integral.unit_isIso ((aE.integral.completedFunctor l E).obj K)
  have ho := IsIso.inv_eq_inv.mpr (pbcScalarOrdinaryPull_comp l E F i g h K.obj)
  simp only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app, NatIso.inv_inv_app,
    Category.assoc] at ho
  have ho' :
      (rationalScalarOrdinaryBeta l E F i h).hom.app
          ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj) ≫
        H.map ((rationalScalarOrdinaryBeta l E F i g).hom.app K.obj) =
      C.map ((pbcActualDerivedPullCompIso h g (pbcIntegralDatum l E)).inv.app K.obj) ≫
        (rationalScalarOrdinaryBeta l E F i (h ≫ g)).hom.app K.obj ≫
        (pbcActualDerivedPullCompIso h g (pbcIntegralDatum l F)).hom.app T.obj := ho
  have hn := (rationalScalarOrdinaryBeta l E F i h).hom.naturality
    ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj)
  have hu := (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l F) h).naturality
    ((rationalScalarStrictBeta l E F i g).hom.app K.obj)
  simp only [Functor.comp_map] at hn hu
  exact mixed_cancel_pasting
    (C.map ((pbcActualDerivedPull h (pbcIntegralDatum l E)).map
      ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj)))
    (C.map ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) h).app
      ((aE.integral.completedFunctor l E).obj K).obj))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((pbcActualDerivedPullCompIso h g (pbcIntegralDatum l F)).hom_inv_id_app T.obj)
    (mixed_map_three C (uE K))
    (rationalScalarCompletionUnitSquare l E F i (h ≫ g) K.obj).1
    (rationalScalarCompletionUnitSquare l E F i h
      ((aE.integral.completedFunctor l E).obj K).obj).1 hn hu.symm
    (mixed_map_two H (rationalScalarCompletionUnitSquare l E F i g K.obj).1)
    (uF T) ho'


end AlgebraicGeometry.Scheme
