/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SixFunctors.Compact.CompactSupportProjectionFiniteStages
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
import WeilConjectures.SixFunctors.Integral.IntegralStageProjectionStructuralIdentities
import WeilConjectures.SixFunctors.FixProjectionCompactification.FixProjectionCompactificationComparison

/-! # Integral coefficient projection laws

The integral part of the compact-support projection formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open CategoryTheory.SuppliedExchangeProjection

namespace WeilConjectures

private theorem transported_bifunctor_component
    {A B : Type v} [Category.{w} A] [Category.{w} B]
    {F F' G' G : A ⥤ B ⥤ B} (e : F = F') (e' : G' = G)
    (τ : F' ⟶ G') (K : A) (L : B) :
    ((eqToHom e ≫ τ ≫ eqToHom e').app K).app L =
      eqToHom (congrArg (fun H : A ⥤ B ⥤ B ↦ (H.obj K).obj L) e) ≫
        (τ.app K).app L ≫
        eqToHom (congrArg (fun H : A ⥤ B ⥤ B ↦ (H.obj K).obj L) e') := by
  subst F'
  subst G
  simp

private theorem projection_naturality
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    (A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    {K K' : B X} {L L' : B Y} (a : K ⟶ K') (b : L ⟶ L') :
    ((T Y).map ((S.support f c).map a)).app L ≫
        ((T Y).obj ((S.support f c).obj K')).map b ≫
        compactSupportProjectionComponent A f c K' L' =
      compactSupportProjectionComponent A f c K L ≫
        (S.support f c).map
          (((T X).map a).app ((S.pull f).obj L) ≫
            ((T X).obj K').map ((S.pull f).map b)) := by
  let Q := compactSupportProjectionSquare f c
  let d := A Q
  let V := (Functor.postcompose₂.obj (S.support f c)).obj
    ((((Functor.whiskeringLeft₂ (B X)).obj (𝟭 (B X))).obj (S.pull f)).obj (T X))
  let τ : S.support f c ⋙ T Y ⟶ V :=
    eqToHom (by rw [d.compactSupport, d.tensorY]; rfl) ≫ d.stage.projection ≫
      eqToHom (by rw [d.compactSupport, d.tensorX, d.pull]; rfl)
  have hτ (M : B X) (N : B Y) :
      (τ.app M).app N = compactSupportProjectionComponent A f c M N := by
    have h := transported_bifunctor_component
      (F := S.support f c ⋙ T Y) (G := V)
      (by rw [d.compactSupport, d.tensorY]; rfl)
      (by rw [d.compactSupport, d.tensorX, d.pull]; rfl)
      d.stage.projection M N
    dsimp only [τ, Q, d, V, compactSupportProjectionComponent,
      SixFunctorExchangeData.projectionComponent, compactSupportProjectionSquare,
      Functor.comp_obj, Functor.postcompose₂, Functor.whiskeringLeft₂] at h ⊢
    exact h
  have h₁ := congrArg (fun t ↦ t.app L) (τ.naturality a)
  have h₂ := (τ.app K').naturality b
  change ((T Y).map ((S.support f c).map a)).app L ≫ (τ.app K').app L =
    (τ.app K).app L ≫ (S.support f c).map (((T X).map a).app ((S.pull f).obj L)) at h₁
  change ((T Y).obj ((S.support f c).obj K')).map b ≫ (τ.app K').app L' =
    (τ.app K').app L ≫ (S.support f c).map
      (((T X).obj K').map ((S.pull f).map b)) at h₂
  simp only [← hτ]
  rw [h₂, ← Category.assoc, h₁, Category.assoc, ← Functor.map_comp]

end WeilConjectures
