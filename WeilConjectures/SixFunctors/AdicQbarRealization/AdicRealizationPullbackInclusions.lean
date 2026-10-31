/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationB
public import Mathlib.NumberTheory.Padics.Complex
import WeilConjectures.SixFunctors.Common.CommonStagePullbackNormalizedDescent

/-! # Pullback on finite-stage inclusions

Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
(blueprint: lem-sf-adic-realization-pullback-inclusions)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false

universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (inclusion stageSystem)

attribute [local irreducible] HasDerivedCategory.standard integralDerivedPullback

private theorem morphism_inclusion_eq
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)]
    {D : I → Type*} [∀ i, Category (D i)]
    {S : StageSystem C} {T : StageSystem D} (F : S.Morphism T) (i : I) :
    S.ι i ⋙ F.functor = F.Φ i ⋙ T.ι i := by
  refine CategoryTheory.Functor.hext (F := S.ι i ⋙ F.functor)
    (G := F.Φ i ⋙ T.ι i) (fun _ ↦ rfl) ?_
  intro K L f
  exact heq_of_eq (F.functor_map_ι f)

/-- The chosen pullback restricts to its prescribed rational stage functor.
Source: normalized descent (blueprint: lem-sf-adic-realization-pullback-inclusions). -/
theorem realizationPullback_inclusion_eq (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (E : Index l (PadicAlgCl l)) :
    inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙
        commonStageDerivedPullback l (PadicAlgCl l) g =
      rationalDerivedPullback l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        inclusion (l := l) (Ω := PadicAlgCl l) (Y := X) E := by
  obtain ⟨hc, he⟩ := commonStagePullbackNormalizedDescent l (PadicAlgCl l) g
  rw [he]
  exact morphism_inclusion_eq _ E

/-- Integral localization intertwines the prescribed integral and rational pullbacks.
Source: rational pullback normalization
(blueprint: lem-sf-adic-realization-pullback-inclusions). -/
theorem realizationPullback_localization_eq (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E : Index l (PadicAlgCl l)) :
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) Y ⋙
        rationalDerivedPullback l (Coefficient.{u} l (PadicAlgCl l) E) g =
      constructibleIntegralPullback l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X := by
  let h := (rationalDerivedPullback_existsUnique l
    (Coefficient.{u} l (PadicAlgCl l) E) g).exists.choose_spec
  refine CategoryTheory.Functor.hext (fun K ↦ h.2.1 _) ?_
  intro K L f
  exact h.2.2 K L f 1

/-- Complete-input inverse image agrees with the tower-defined integral pullback.
Source: the specified completion-unit comparison and its naturality laws
(blueprint: lem-sf-adic-realization-pullback-inclusions). -/
@[irreducible] def realizationCompletionPullbackIso (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (E : Index l (PadicAlgCl l)) :
    (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) Y).ι ⋙
        podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g ≅
      constructibleIntegralPullback l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι :=
  NatIso.ofComponents
    (fun K ↦ podCompletedToTowerIso l (Coefficient.{u} l (PadicAlgCl l) E) g K)
    (fun {K L} f ↦ (podCompletedToTower_laws l
      (Coefficient.{u} l (PadicAlgCl l) E) g).1 K.obj L.obj f.hom)

/-- The inverse component is the prescribed complete-input comparison.
Source: construction of the preceding isomorphism
(blueprint: lem-sf-adic-realization-pullback-inclusions). -/
theorem realizationCompletionPullbackIso_inv_app (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (E : Index l (PadicAlgCl l))
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y) :
    (realizationCompletionPullbackIso l g E).inv.app K =
      (podCompletedToTowerIso l (Coefficient.{u} l (PadicAlgCl l) E) g K).inv := by
  delta realizationCompletionPullbackIso
  rfl

end WeilConjectures.AdicQbarRealization
