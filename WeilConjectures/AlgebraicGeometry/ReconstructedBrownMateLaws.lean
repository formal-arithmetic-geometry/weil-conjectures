/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ReconstructedPairRefinementData

/-! # Reconstructed BrownMateLaws

Source: blueprint sk-prop-sp-unique-adjoint, categorical proof, and
sk-thm-purity-transport Steps 2--4
(blueprint: lem-pur-reconstructed-brown-mate-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] WeilConjectures.integralExceptionalSystemDerived
attribute [-instance] WeilConjectures.integralExceptionalLevelDerived
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open WeilConjectures CompactSupportCondensedRealization PurIntegralSupportComparison
namespace WeilConjectures.ReconstructedPairRefinement
variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  (C : ComparisonFamily l k)
  (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
  [f.IsOver (Spec (.of k))]

attribute [local irreducible] systemRefinement coordinates
  PurIntegralSupportComparison.beta systemDown systemComparison mate
  PurIntegralRepresentingPair.transpose PurIntegralRepresentingPair.supportPresentation

/-- Coordinate conjugation preserves composition by cancellation of the middle isomorphisms. -/
private theorem conjugate_comp
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ B) (v : C ⥤ D) (F G H : B ⥤ D) (F' G' H' : A ⥤ C)
    (a : e.functor ⋙ F ≅ F' ⋙ v) (b : e.functor ⋙ G ≅ G' ⋙ v)
    (c : e.functor ⋙ H ≅ H' ⋙ v) (s : F' ⟶ G') (t : G' ⟶ H') :
    conjugate e v F H F' H' a c (s ≫ t) =
      conjugate e v F G F' G' a b s ≫ conjugate e v G H G' H' b c t := by
  ext K
  unfold conjugate conjugateComponent
  dsimp only [NatTrans.comp_app]
  rw [v.map_comp]
  simp only [Category.assoc]
  rw [← G.map_comp_assoc, Iso.hom_inv_id_app]
  dsimp only [CategoryTheory.Functor.comp_obj]
  rw [G.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app_assoc]

/-- Inverse transposes are inverse arrows, using the two injective counit maps. -/
private theorem mates_inverse
    {A B : Type*} [Category A] [Category B] (F G : A ⥤ B) (q : G ⟶ F)
    {M N : A} {L : B} [IsIso (q.app M)] [IsIso (q.app N)]
    (t : F.obj M ⟶ L) (s : G.obj N ⟶ L) (a : N ⟶ M) (b : M ⟶ N)
    (ha : F.map a ≫ t = inv (q.app N) ≫ s)
    (hb : G.map b ≫ s = q.app M ≫ t)
    (hF : Function.Injective (fun z : M ⟶ M ↦ F.map z ≫ t))
    (hG : Function.Injective (fun z : N ⟶ N ↦ G.map z ≫ s)) : IsIso a := by
  have hab : a ≫ b = 𝟙 N := by
    apply hG
    change G.map (a ≫ b) ≫ s = G.map (𝟙 N) ≫ s
    rw [Functor.map_comp, Category.assoc, hb, q.naturality_assoc, ha]
    simp
  have hba : b ≫ a = 𝟙 M := by
    apply hF
    apply (cancel_epi (q.app M)).1
    change q.app M ≫ (F.map (b ≫ a) ≫ t) = q.app M ≫ (F.map (𝟙 M) ≫ t)
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [← q.naturality_assoc, ha, IsIso.hom_inv_id_assoc, hb]
    simp
  exact ⟨⟨b, hab, hba⟩⟩

/-- A composite of transposes has the transpose of the composite comparison. -/
private theorem mates_comp
    {A B : Type*} [Category A] [Category B] (F G H : A ⥤ B)
    (q : G ⟶ F) (r : H ⟶ G) (p : H ⟶ F) (hp : p = r ≫ q)
    {M N O : A} {L : B} [IsIso (q.app N)] [IsIso (r.app O)] [IsIso (p.app O)]
    (t : F.obj M ⟶ L) (s : G.obj N ⟶ L) (v : H.obj O ⟶ L)
    (a : N ⟶ M) (b : O ⟶ N) (c : O ⟶ M)
    (ha : F.map a ≫ t = inv (q.app N) ≫ s)
    (hb : G.map b ≫ s = inv (r.app O) ≫ v)
    (hc : F.map c ≫ t = inv (p.app O) ≫ v)
    (hF : Function.Injective (fun z : O ⟶ M ↦ F.map z ≫ t)) : c = b ≫ a := by
  apply hF
  apply (cancel_epi (p.app O)).1
  change p.app O ≫ (F.map c ≫ t) = p.app O ≫ (F.map (b ≫ a) ≫ t)
  rw [hc, IsIso.hom_inv_id_assoc]
  rw [hp, NatTrans.comp_app, Functor.map_comp]
  simp only [Category.assoc]
  rw [← q.naturality_assoc, ha, IsIso.hom_inv_id_assoc, hb, IsIso.hom_inv_id_assoc]

variable {l E k C X Y f}

/-- The published Brown Hom formula makes composition with the counit injective. -/
private theorem hom_injective {c : Compactification f} (D : At l E k C X Y f c)
    (L : CondensedERealization.Integral l E Y.scheme) (A : D.Supplied L)
    (B : DerivedCategory (BrownTowerComparison.ProSystem X.scheme
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E)))
    (hB : D.transport.siteX.Origin B) :
    Function.Injective (fun a : B ⟶ D.output L ↦
      D.transport.compact.functor.map a ≫ D.counit L A) := by
  have := D.transport.finite
  intro a b h
  apply (D.transport.hom _ (D.pair L A).origin (D.pair L A).normalized
    (D.pair L A).finiteTor (D.pair L A).lowerBound B hB).injective
  simpa only [D.normalized.hom_formula, At.counit] using h

/-- The defining inverse Hom image of the mate satisfies its prescribed counit equation. -/
private theorem mate_counit {c d : Compactification f}
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d)
    (L : CondensedERealization.Integral l E Y.scheme)
    (A₁ : D₁.Supplied L) (A₂ : D₂.Supplied L)
    [IsIso ((systemDown D₁ D₂ w).app (D₂.output L))] :
    D₁.transport.compact.functor.map (mate D₁ D₂ w L A₁ A₂) ≫ D₁.counit L A₁ =
      inv ((systemDown D₁ D₂ w).app (D₂.output L)) ≫ D₂.counit L A₂ := by
  have := D₁.transport.finite
  have he := (D₁.transport.hom _ (D₁.pair L A₁).origin (D₁.pair L A₁).normalized
    (D₁.pair L A₁).finiteTor (D₁.pair L A₁).lowerBound _
    (output_origin D₁ D₂ L A₂)).apply_symm_apply
    ((systemComparison D₁ D₂ w (D₂.output L) (output_origin D₁ D₂ L A₂)).hom ≫
      D₂.counit L A₂)
  rw [D₁.normalized.hom_formula] at he
  simpa only [mate, At.counit, systemComparison, Iso.symm_hom, asIso_inv] using he

variable (l E k C X Y f)

/-- Invertibility and composition of the actual transported Brown mates.
Source: blueprint sk-prop-sp-unique-adjoint categorical proof, Transposes and
Uniqueness; parent proof Steps 4 and 6.
Proof: the Brown Hom formula sends each defined mate to its prescribed system
comparison followed by the second counit. Define the reverse arrow by transposing
the inverse system comparison followed by the first counit under the second Hom
bijection. Both outputs lie in the common intrinsic origin domain. Naturality of
the system comparison and the two counit equations show that each composite has
the same transpose as the identity. Injectivity of the Brown Hom bijections proves
they are inverse. For three compactifications transpose the composite of mates;
use both counit equations, naturality, and composition of the intrinsic refinement
maps conjugated by beta. The resulting transpose is that of the direct mate, so
injectivity proves composition. These are equations of system maps.
(blueprint: lem-pur-reconstructed-brown-mate-laws). -/
theorem reconstructedBrownMateLaws :
    (∀ (c d : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (w : c.Refinement d)
    (L : CondensedERealization.Integral l E Y.scheme)
    (A₁ : D₁.Supplied L) (A₂ : D₂.Supplied L), IsIso (mate D₁ D₂ w L A₁ A₂)) ∧
    (∀ (c d e : Compactification f)
    (D₁ : At l E k C X Y f c) (D₂ : At l E k C X Y f d) (D₃ : At l E k C X Y f e)
    (r : c.Refinement d) (s : d.Refinement e)
    (L : CondensedERealization.Integral l E Y.scheme)
    (A₁ : D₁.Supplied L) (A₂ : D₂.Supplied L) (A₃ : D₃.Supplied L),
    mate D₁ D₃ (r.comp s) L A₁ A₃ = mate D₂ D₃ s L A₂ A₃ ≫ mate D₁ D₂ r L A₁ A₂) := by
  constructor
  · intro c d D₁ D₂ w L A₁ A₂
    have := D₂.transport.finite
    let b := (D₂.transport.hom _ (D₂.pair L A₂).origin (D₂.pair L A₂).normalized
      (D₂.pair L A₂).finiteTor (D₂.pair L A₂).lowerBound _
      (output_origin D₂ D₁ L A₁)).symm
      ((systemDown D₁ D₂ w).app (D₁.output L) ≫ D₁.counit L A₁)
    have hb : D₂.transport.compact.functor.map b ≫ D₂.counit L A₂ =
        (systemDown D₁ D₂ w).app (D₁.output L) ≫ D₁.counit L A₁ := by
      have h := (D₂.transport.hom _ (D₂.pair L A₂).origin (D₂.pair L A₂).normalized
        (D₂.pair L A₂).finiteTor (D₂.pair L A₂).lowerBound _
        (output_origin D₂ D₁ L A₁)).apply_symm_apply
        ((systemDown D₁ D₂ w).app (D₁.output L) ≫ D₁.counit L A₁)
      rw [D₂.normalized.hom_formula] at h
      exact h
    let := systemDown_isIso D₁ D₂ w _ (output_origin D₁ D₁ L A₁)
    let := systemDown_isIso D₁ D₂ w _ (output_origin D₁ D₂ L A₂)
    exact mates_inverse _ _ (systemDown D₁ D₂ w) _ _ _ b
      (mate_counit D₁ D₂ w L A₁ A₂) hb
      (hom_injective D₁ L A₁ _ (output_origin D₁ D₁ L A₁))
      (hom_injective D₂ L A₂ _ (output_origin D₂ D₂ L A₂))
  · intro c d e D₁ D₂ D₃ r s L A₁ A₂ A₃
    have hp : systemDown D₁ D₃ (r.comp s) =
        systemDown D₂ D₃ s ≫ systemDown D₁ D₂ r := by
      unfold systemDown
      rw [systemRefinement_comp]
      exact conjugate_comp _ _ _ _ _ _ _ _ _ _ _ _ _
    let := systemDown_isIso D₁ D₂ r _ (output_origin D₁ D₂ L A₂)
    let := systemDown_isIso D₂ D₃ s _ (output_origin D₂ D₃ L A₃)
    let := systemDown_isIso D₁ D₃ (r.comp s) _ (output_origin D₁ D₃ L A₃)
    exact mates_comp _ _ _ (systemDown D₁ D₂ r) (systemDown D₂ D₃ s)
      (systemDown D₁ D₃ (r.comp s)) hp _ _ _ _ _ _
      (mate_counit D₁ D₂ r L A₁ A₂) (mate_counit D₂ D₃ s L A₂ A₃)
      (mate_counit D₁ D₃ (r.comp s) L A₁ A₃)
      (hom_injective D₁ L A₁ _ (output_origin D₁ D₃ L A₃))

end WeilConjectures.ReconstructedPairRefinement
