/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y9
-/
module

public import Sheaf.Paper.FiniteStageRationalExchangeData
public import Sheaf.CategoryTheory.StageSystemKaroubi

/-! # Supported extension on the actual coefficient systems

Source: sketch32, lines 1208--1228 and 1291--1321.
(blueprint: lem-sbc-finite-stage-karoubi-extension)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Idempotents AlgebraicGeometry WeilConjectures
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.FiniteStageRationalExchange

private theorem composition_adapter {A B C : Type*}
    [Category* A] [Category* B] [Category* C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C) (a : F ⋙ G ≅ H) :
    (functorExtension₂ _ _).mapIso a =
      (coefficientCompositionIso F G).symm ≪≫ (functorExtension₂ _ _).mapIso a := by
  unfold coefficientCompositionIso
  exact (Iso.refl_trans _).symm

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
variable {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
  [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim V ≤ n)]
  [Fact (∀ x : U, IsUnit (l : U.presheaf.stalk x))]
  [Fact (∀ x : V, IsUnit (l : V.presheaf.stalk x))]
/-- The actual system has the same transitions and associators as supported extension. -/
theorem karSystem_eq (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))] :
    StageSystem.karSystem (pbcAmbientCompleteRawSystem l Ω W) =
      pbcAmbientCompleteSystem l Ω W := by
  apply StageSystem.system_ext
    (S := StageSystem.karSystem (pbcAmbientCompleteRawSystem l Ω W))
    (T := pbcAmbientCompleteSystem l Ω W)
  · unfold StageSystem.karSystem pbcAmbientCompleteSystem
    rfl
  · unfold StageSystem.karSystem pbcAmbientCompleteSystem
    apply heq_of_eq
    funext E M N a b
    unfold pbcAmbientCompleteKaroubiAssociator
    unfold coefficientAssociatorIso
    rfl

/-- The supported morphism and its formulas on the actual coefficient systems. -/
theorem completeKarMorphism_exists
    (F : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω U)
      (pbcAmbientCompleteRawSystem l Ω V))
    (hu : ∀ E, HEq (F.β (le_refl E)) (Iso.refl (F.Φ E))) :
    ∃ K : StageSystem.Morphism (pbcAmbientCompleteSystem l Ω U)
      (pbcAmbientCompleteSystem l Ω V), StageSystem.KarMorphismSpec F K := by
  exact StageSystem.karMorphism_exists (karSystem_eq l Ω U) (karSystem_eq l Ω V) F
    (fun E ↦ (pbcAmbientCompleteRaw_laws l Ω U
      (le_refl E) (le_refl E) (le_refl E)).2.1)
    (fun E ↦ (pbcAmbientCompleteRaw_laws l Ω V
      (le_refl E) (le_refl E) (le_refl E)).2.1) hu

/-- Extend the compatible raw exchange, retaining the formulas and both units. -/
theorem completeKarHom_exists
    {F G : StageSystem.Morphism (pbcAmbientCompleteRawSystem l Ω U)
      (pbcAmbientCompleteRawSystem l Ω V)} (α : StageSystem.Morphism.Hom F G)
    (uF : ∀ E, HEq (F.β (le_refl E)) (Iso.refl (F.Φ E)))
    (uG : ∀ E, HEq (G.β (le_refl E)) (Iso.refl (G.Φ E))) :
    ∃ (K L : StageSystem.Morphism (pbcAmbientCompleteSystem l Ω U)
      (pbcAmbientCompleteSystem l Ω V)), ∃ η : StageSystem.Morphism.Hom K L,
      StageSystem.KarMorphismSpec F K ∧ StageSystem.KarMorphismSpec G L ∧
      ∀ E, HEq (η.τ E) ((functorExtension₂ _ _).map (α.τ E)) := by
  exact StageSystem.karHom_exists (karSystem_eq l Ω U) (karSystem_eq l Ω V) α
    (fun E ↦ (pbcAmbientCompleteRaw_laws l Ω U
      (le_refl E) (le_refl E) (le_refl E)).2.1)
    (fun E ↦ (pbcAmbientCompleteRaw_laws l Ω V
      (le_refl E) (le_refl E) (le_refl E)).2.1) uF uG

end AlgebraicGeometry.Scheme.FiniteStageRationalExchange
