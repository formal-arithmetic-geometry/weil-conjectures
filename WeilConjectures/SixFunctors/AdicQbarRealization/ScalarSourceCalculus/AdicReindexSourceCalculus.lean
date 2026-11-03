/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexSourceConstruction
import WeilConjectures.SixFunctors.AdicQbarRealization.CommonStageIntegralScalarArrow
import WeilConjectures.AlgebraicGeometry.Rational.RationalScalarBalancedLocalization

/-! # Component calculations for the source realization comparison

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-adic-reindex-source-calculus)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option cleanup.letToHave false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
attribute [local irreducible] HasDerivedCategory.standard
  derivedPull LocallyFiniteAdicRealization.sections
  LocallyFiniteAdicRealization.CoefficientPresentation.integralMap
  podCompletedDerivedInverseImage integralDerivedPullback
  commonStageDerivedPullback rationalDerivedPullback

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (inclusion stageSystem integralTransition)

namespace ScalarSourceCalculus

section StageCalculus
attribute [local implicit_reducible] StageSystem.ι StageSystem.Morphism.functor
  StageSystem.instCategoryPairCategory GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.pairCategory
  integralScalarExtensionOfUniverses

private theorem map_transport_middle
    {C D A : Type*} [Category C] [Category D] [Category A]
    (F : C ⥤ D) (T : A ⥤ C) {X : C} {Y Y' : A} (e : Y = Y')
    (f : X ⟶ T.obj Y) {U V W : D} (r : F.obj X ⟶ U)
    (s : U ⟶ V) (t : V ⟶ W) (v : W ⟶ F.obj (T.obj Y'))
    (h : HEq (F.map f) (r ≫ s ≫ t ≫ v)) :
    F.map (f ≫ T.map (eqToHom e)) = r ≫ (s ≫ t) ≫ v := by
  cases e
  rw [eqToHom_refl, T.map_id, Category.comp_id]
  simpa only [Category.assoc] using eq_of_heq h

theorem transport_square
    {C : Type*} [Category C] {A B A' B' : C}
    (f : A ⟶ B) (g : A' ⟶ B') (eA : A = A') (eB : B = B')
    (h : HEq f g) : f ≫ eqToHom eB = eqToHom eA ≫ g := by
  subst A' B'
  simpa using eq_of_heq h

theorem scalar_source_paste
    {C D N : Type*} [Category C] [Category D] [Category N]
    (NE : C ⥤ N) (NL : D ⥤ N) (T : C ⥤ D)
    (n : ∀ M : C, NE.obj M ⟶ NL.obj (T.obj M))
    {E P : C} {F Q M Z : D} {A B : N} (p : E ≅ P) (q : F ≅ Q)
    (r : A ⟶ NE.obj P) (s : B ⟶ NL.obj Q) (f : A ⟶ B)
    (χ : T.obj P ⟶ M) (δ : M ⟶ Q) (b : T.obj E ⟶ Z) (c : Z ⟶ F)
    (hn : NE.map p.inv ≫ n E = n P ≫ NL.map (T.map p.inv))
    (hhead : f ≫ s = r ≫ n P ≫ NL.map χ ≫ NL.map δ)
    (hsquare : T.map p.hom ≫ χ ≫ δ = b ≫ c ≫ q.hom) :
    f ≫ s ≫ NL.map q.inv =
      r ≫ NE.map p.inv ≫ n E ≫ NL.map b ≫ NL.map c := by
  have hs : χ ≫ δ ≫ q.inv = T.map p.inv ≫ b ≫ c := by
    apply (cancel_epi (T.map p.hom)).1
    simp only [← Category.assoc, ← T.map_comp, Iso.hom_inv_id, T.map_id,
      Category.id_comp]
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun z ↦ z ≫ q.inv) hsquare
  rw [← Category.assoc f s, hhead]
  simp only [Category.assoc, ← NL.map_comp]
  rw [hs]
  simp only [NL.map_comp]
  rw [← Category.assoc (NE.map p.inv), hn]
  simp only [Category.assoc]

/-- Paste the scalar square using only the needed normalization components. -/
theorem scalar_source_square
    {C D N : Type*} [Category C] [Category D] [Category N]
    (NE : C ⥤ N) (NL : D ⥤ N) (T : C ⥤ D)
    (n : ∀ M : C, NE.obj M ⟶ NL.obj (T.obj M))
    {E P : C} {F Q M Z : D} {A B U V : N} (p : E ≅ P) (q : F ≅ Q)
    (r₀ : A ⟶ U) (r₁ : U ⟶ NE.obj P)
    (s₀ : B ⟶ V) (s₁ : V ⟶ NL.obj Q) (f : A ⟶ B)
    (χ : T.obj P ⟶ M) (δ : M ⟶ Q) (b : T.obj E ⟶ Z) (c : Z ⟶ F)
    (srcE : A ⟶ NE.obj E) (srcL : B ⟶ NL.obj F)
    (hE : srcE = r₀ ≫ r₁ ≫ NE.map p.inv)
    (hL : srcL = s₀ ≫ s₁ ≫ NL.map q.inv)
    (hn : NE.map p.inv ≫ n E = n P ≫ NL.map (T.map p.inv))
    (hhead : f ≫ s₀ ≫ s₁ = r₀ ≫ r₁ ≫ n P ≫ NL.map χ ≫ NL.map δ)
    (hsquare : T.map p.hom ≫ χ ≫ δ = b ≫ c ≫ q.hom) :
    f ≫ srcL = srcE ≫ n E ≫ NL.map b ≫ NL.map c := by
  rw [hE, hL]
  simpa only [Category.assoc] using
    scalar_source_paste NE NL T n p q (r₀ ≫ r₁) (s₀ ≫ s₁) f χ δ b c hn
      (by simpa only [Category.assoc] using hhead) hsquare

/-- The maps in scalar source pasting, stored without unfolding concrete derived models. -/
structure ScalarSourceMaps (C D N : Type*) [Category C] [Category D] [Category N] where
  NE : C ⥤ N
  NL : D ⥤ N
  T : C ⥤ D
  E : C
  P : C
  F : D
  Q : D
  M : D
  Z : D
  A : N
  B : N
  U : N
  V : N
  p : E ≅ P
  q : F ≅ Q
  r₀ : A ⟶ U
  r₁ : U ⟶ NE.obj P
  s₀ : B ⟶ V
  s₁ : V ⟶ NL.obj Q
  f : A ⟶ B
  χ : T.obj P ⟶ M
  δ : M ⟶ Q
  b : T.obj E ⟶ Z
  c : Z ⟶ F
  srcE : A ⟶ NE.obj E
  srcL : B ⟶ NL.obj F
  n : ∀ K : C, NE.obj K ⟶ NL.obj (T.obj K)
  naturality : NE.map p.inv ≫ n E = n P ≫ NL.map (T.map p.inv)

/-- The stored maps with the two proved source-component formulas. -/
structure ScalarSourceDiagram (C D N : Type*) [Category C] [Category D] [Category N]
    extends ScalarSourceMaps C D N where
  sourceE : srcE = r₀ ≫ r₁ ≫ NE.map p.inv
  sourceL : srcL = s₀ ≫ s₁ ≫ NL.map q.inv

/-- Pasting using the stored categorical maps. -/
theorem ScalarSourceDiagram.square
    {C D N : Type*} [Category C] [Category D] [Category N]
    (d : ScalarSourceDiagram C D N)
    (hhead : d.f ≫ d.s₀ ≫ d.s₁ =
      d.r₀ ≫ d.r₁ ≫ d.n d.P ≫ d.NL.map d.χ ≫ d.NL.map d.δ)
    (hsquare : d.T.map d.p.hom ≫ d.χ ≫ d.δ = d.b ≫ d.c ≫ d.q.hom) :
    d.f ≫ d.srcL = d.srcE ≫ d.n d.E ≫ d.NL.map d.b ≫ d.NL.map d.c := by
  exact scalar_source_square d.NE d.NL d.T d.n d.p d.q
    d.r₀ d.r₁ d.s₀ d.s₁ d.f d.χ d.δ d.b d.c d.srcE d.srcL
    d.sourceE d.sourceL d.naturality hhead hsquare

/-- Naturality of the existing scalar balancing map, in the inverse direction. -/
theorem normalization_inv_naturality
    {W : Scheme.{u}} {R S B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    {K L : DerivedCategory (pbcModules W R)} (f : K ⟶ L) :
    (pbcDerivedExtend χ).map f ≫ (pbcReductionNormalization φ ψ χ h L).inv =
      (pbcReductionNormalization φ ψ χ h K).inv ≫
        (pbcDerivedExtend ψ).map ((pbcDerivedExtend φ).map f) := by
  have hn := rationalBalancedDerivedNaturality φ ψ χ h f
  apply (cancel_epi (pbcReductionNormalization φ ψ χ h K).hom).1
  rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [Iso.hom_inv_id_assoc]

theorem pullback_scalar_arrow (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y) :
    HEq ((commonStageDerivedPullback l (PadicAlgCl l) g).map
      (realizationScalarArrow l Y E L h K))
      (realizationScalarArrow l X E L h
          ((constructibleIntegralPullback l (Coefficient.{u} l (PadicAlgCl l) E) g).obj K) ≫
        (inclusion (l := l) (Ω := PadicAlgCl l) (Y := X) L).map
          ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) L) X).map
            (integralPullbackScalarComparison l (Coefficient.{u} l (PadicAlgCl l) E)
              (Coefficient.{u} l (PadicAlgCl l) L)
              (coefficientInclusion l (PadicAlgCl l) E L h) g K).hom)) := by
  exact commonStageIntegralScalarArrow l (PadicAlgCl l) g E L h K
    (realizationStageObject_eq l Y E L h K)
    (realizationStageObject_eq l X E L h
      ((constructibleIntegralPullback l (Coefficient.{u} l (PadicAlgCl l) E) g).obj K))

end StageCalculus

attribute [local implicit_reducible] StageSystem.ι
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.pairCategory
  integralScalarExtensionOfUniverses

theorem ordinary_scalar_arrow (l : ℕ) [Fact l.Prime] (W : Scheme.{u})
    (R : LocallyFiniteAdicRealization.Realization l W)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) W) :
    (ordinary l W R).map (realizationScalarArrow l W E L h K) =
      (R.integral E).hom.app K ≫ nativeScalarTransition l W R E L h K.obj ≫
        (R.integral L).inv.app
          ((integralTransition l (PadicAlgCl l) W E L h).obj K) := by
  exact map_transport_middle (ordinary l W R)
    (inclusion (l := l) (Ω := PadicAlgCl l) (Y := W) L)
    (realizationStageObject_eq l W E L h K)
    (((stageSystem l (PadicAlgCl l) W).isoToStage
      ((inclusion (l := l) (Ω := PadicAlgCl l) (Y := W) E).obj
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) W).obj K))
      h).hom) _ _ _ _ (R.common_field E L h K)

theorem source_hom (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (R : LocallyFiniteAdicRealization.Realization l X) (E : Index l (PadicAlgCl l))
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y) :
    let QY := sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) Y
    let IX := inclusion (l := l) (Ω := PadicAlgCl l) (Y := X) E
    let e := (congrArg (fun Z ↦ QY ⋙ Z) (realizationPullback_inclusion_eq l g E)).trans
      (congrArg (fun Z ↦ Z ⋙ IX) (realizationPullback_localization_eq l g E))
    (realizationReindexSource l g R E).hom.app K =
      (ordinary l X R).map (eqToHom (Functor.congr_obj e K)) ≫
        (R.integral E).hom.app ((constructibleIntegralPullback l
          (Coefficient.{u} l (PadicAlgCl l) E) g).obj K) ≫
        (pbcDerivedExtend (coefficientMap l X R E)).map
          ((podCompletedToTowerIso l (Coefficient.{u} l (PadicAlgCl l) E) g K).inv) := by
  dsimp only
  delta realizationReindexSource
  dsimp only
  erw [realizationReindexSourceComposite_hom]
  congr 2
  exact congrArg _ (realizationCompletionPullbackIso_inv_app l g E K)

end ScalarSourceCalculus
end WeilConjectures.AdicQbarRealization
