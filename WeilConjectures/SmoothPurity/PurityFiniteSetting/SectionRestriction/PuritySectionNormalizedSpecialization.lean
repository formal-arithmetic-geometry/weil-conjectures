/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionRestrictionData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PurityConstantFamilyBaseChange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PurityRankZeroFamilyReadings

/-! # Naturality of normalized DNC specialization

Source: blueprint latest, sec-smooth-purity, orientation charts Step 3 and
composition coherence Step 1 (blueprint: lem-pur-section-normalized-specialization).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.SectionRestriction

private theorem counit_naturality {C D : Type*} [Category C] [Category D]
    (A : C ⥤ D) (E : D ⥤ C) (ε : A ⋙ E ≅ 𝟭 C)
    {X Y : C} (c : X ≅ Y) :
    E.mapIso (A.mapIso c) ≪≫ ε.app Y = ε.app X ≪≫ c := by
  apply Iso.ext
  exact ε.hom.naturality c.hom

private theorem reading_naturality {C D : Type*} [Category C] [Category D]
    (A : C ⥤ D) (E : D ⥤ C) (ε : A ⋙ E ≅ 𝟭 C)
    {F' : D} {X X' : C} (κ' : F' ≅ A.obj X')
    (c : X' ≅ X) :
    E.mapIso (κ' ≪≫ A.mapIso c) ≪≫ ε.app X =
      (E.mapIso κ' ≪≫ ε.app X') ≪≫ c := by
  rw [Functor.mapIso_trans, Iso.trans_assoc, counit_naturality, Iso.trans_assoc]

private theorem ratio_square {C : Type*} [Category C]
    {F F' X X' N N' : C} (r : F ≅ X) (r' : F' ≅ X')
    (θ : F ≅ N) (θ' : F' ≅ N') (T : F ≅ F') (c : X ≅ X') (n : N ≅ N')
    (hr : r ≪≫ c = T ≪≫ r') (hθ : T ≪≫ θ' = θ ≪≫ n) :
    (r.symm ≪≫ θ) ≪≫ n = c ≪≫ r'.symm ≪≫ θ' := by
  calc
    (r.symm ≪≫ θ) ≪≫ n = r.symm ≪≫ T ≪≫ θ' := by
      rw [Iso.trans_assoc, ← hθ]
    _ = c ≪≫ r'.symm ≪≫ θ' := by
      have h := congrArg (fun e ↦ r.symm ≪≫ e ≪≫ r'.symm ≪≫ θ') hr
      simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc,
        Iso.self_symm_id_assoc] using h.symm

private theorem normalized_readings_square {C D : Type*} [Category C] [Category D]
    (A : C ⥤ D) (E₁ E₀ : D ⥤ C) (ε₁ : A ⋙ E₁ ≅ 𝟭 C) (ε₀ : A ⋙ E₀ ≅ 𝟭 C)
    {F F' : D} {X X' N N' : C} (κ : F ≅ A.obj X) (κ' : F' ≅ A.obj X')
    (θ₁ : E₁.obj F ≅ X) (θ₁' : E₁.obj F' ≅ X')
    (θ₀ : E₀.obj F ≅ N) (θ₀' : E₀.obj F' ≅ N')
    (T : F' ≅ F) (c : X' ≅ X) (n : N' ≅ N)
    (hκ : E₁.mapIso κ ≪≫ ε₁.app X = θ₁)
    (hκ' : E₁.mapIso κ' ≪≫ ε₁.app X' = θ₁')
    (hfaith : ∀ Y (α β : F' ≅ A.obj Y), E₁.mapIso α = E₁.mapIso β → α = β)
    (h₁ : E₁.mapIso T ≪≫ θ₁ = θ₁' ≪≫ c)
    (h₀ : E₀.mapIso T ≪≫ θ₀ = θ₀' ≪≫ n) :
    ((E₀.mapIso κ' ≪≫ ε₀.app X').symm ≪≫ θ₀') ≪≫ n =
      c ≪≫ (E₀.mapIso κ ≪≫ ε₀.app X).symm ≪≫ θ₀ := by
  have hmodel : κ' ≪≫ A.mapIso c = T ≪≫ κ := by
    apply hfaith X
    have h : E₁.mapIso (κ' ≪≫ A.mapIso c) ≪≫ ε₁.app X =
        E₁.mapIso (T ≪≫ κ) ≪≫ ε₁.app X := by
      rw [reading_naturality, hκ', Functor.mapIso_trans, Iso.trans_assoc, hκ, h₁]
    have h' := congrArg (fun e ↦ e ≪≫ (ε₁.app X).symm) h
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using h'
  have hr : (E₀.mapIso κ' ≪≫ ε₀.app X') ≪≫ c =
      E₀.mapIso T ≪≫ (E₀.mapIso κ ≪≫ ε₀.app X) := by
    rw [← reading_naturality, hmodel, Functor.mapIso_trans, Iso.trans_assoc]
  exact ratio_square _ _ _ _ _ _ _ hr h₀

/-- Normalized specialization respects the fibre squares and is the identity in rank zero.
Source: blueprint latest, sk-thm-dnc Local construction and Gluing, final restriction
(blueprint: lem-pur-section-normalized-specialization).
Proof: use family constancy to obtain kappa and kappa prime normalized by endpointOne.
Conjugate kappa by the family restriction and by the pullback of its one-fibre reading.
The first fibre square makes this isomorphism normalized at one. Uniqueness of the
normalized family isomorphism makes it kappa prime. Restrict at zero, invert, and
use the second fibre square; the DNC normalization formula identifies the two endpoint
readings with delta. This is the first conclusion. Under base change the analogous
conjugate includes the pullback compositor for the line projection. The two base fibre
squares again give normalization at one; uniqueness and restriction at zero give the
second conclusion. For the standard identity section in rank zero, its ideal is zero,
the Rees algebra is R[t], and both geometric projections are isomorphisms. Their
counit-normalized comparisons identify the family with the constant pullback of the
identity section object. This identification is normalized at one, so uniqueness makes
its two readings equal. The canonical collapse of the normal pair therefore gives the
last conclusion. Empty bases and dimension zero require no cancellation of a twist. -/
theorem section_normalized_specialization (P : PurityFiniteSetting.{u})
    (hE :
  ∀ (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d : ℕ) (X' X : Pair B d) (a : EtaleMap X' X),
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso
          (familyRestriction P aB a) ≪≫ endpointOne P aB X =
      endpointOne P aB X' ≪≫ restriction P aB a) ∧
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)).leftDerivedFunctor.mapIso
          (familyRestriction P aB a) ≪≫ endpointZero P aB X =
      endpointZero P aB X' ≪≫ restriction P aB (normalEtaleMap P aB a)))
    (hB :
  ∀ (B B₀ : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB₀ : B₀ ⟶ Spec (.of P.field.k))
    [IsSeparated aB₀] [LocallyOfFiniteType aB₀] [QuasiCompact aB₀]
    (b : B₀ ⟶ B) (_hb : b ≫ aB = aB₀) (d : ℕ)
    (X : Pair B d) (X₀ : Pair B₀ d) (sq : BaseChange b X₀ X),
    (endpointPull P b _ _ (AffineSpace.oneSection_comp_map b)
        (invariant P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) (familyPair X)) ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) B₀)).leftDerivedFunctor.mapIso
          (baseComparison P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB)
            ((AffineSpace (ULift.{u} (Fin 1)) B₀ ↘ B₀) ≫ aB₀)
            (familyBaseChange P aB aB₀ sq)) ≪≫ endpointOne P aB₀ X₀ =
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (endpointOne P aB X) ≪≫ baseComparison P aB aB₀ sq) ∧
    (endpointPull P b _ _ (AffineSpace.zeroSection_comp_map b)
        (invariant P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) (familyPair X)) ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B₀)).leftDerivedFunctor.mapIso
          (baseComparison P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB)
            ((AffineSpace (ULift.{u} (Fin 1)) B₀ ↘ B₀) ≫ aB₀)
            (familyBaseChange P aB aB₀ sq)) ≪≫ endpointZero P aB₀ X₀ =
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (endpointZero P aB X) ≪≫
          baseComparison P aB aB₀ (normalBaseChange P aB aB₀ sq))) :
  (∀ (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d : ℕ) (X' X : Pair B d) (a : EtaleMap X' X),
    (delta P aB X' ≪≫ restriction P aB (normalEtaleMap P aB a) =
      restriction P aB a ≪≫ delta P aB X)) ∧
  (∀ (B B₀ : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB₀ : B₀ ⟶ Spec (.of P.field.k))
    [IsSeparated aB₀] [LocallyOfFiniteType aB₀] [QuasiCompact aB₀]
    (b : B₀ ⟶ B) (_hb : b ≫ aB = aB₀) (d : ℕ)
    (X : Pair B d) (X₀ : Pair B₀ d) (sq : BaseChange b X₀ X),
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (delta P aB X) ≪≫ baseComparison P aB aB₀ (normalBaseChange P aB aB₀ sq) =
      baseComparison P aB aB₀ sq ≪≫ delta P aB₀ X₀)) ∧ RankZero P := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro B aB _ _ _ d X' X a
    obtain ⟨⟨κ, hκ, hδ⟩, _⟩ := section_constant_trivialization P aB X
    obtain ⟨⟨κ', hκ', hδ'⟩, hfaith⟩ := section_constant_trivialization P aB X'
    rw [hδ', hδ]
    exact normalized_readings_square _ _ _
      (lineCounit P B _ (AffineSpace.oneSection_comp_over _ B))
      (lineCounit P B _ (AffineSpace.zeroSection_comp_over _ B))
      κ κ' _ _ _ _ (familyRestriction P aB a) (restriction P aB a)
      (restriction P aB (normalEtaleMap P aB a)) hκ hκ' hfaith
      (hE B aB d X' X a).1 (hE B aB d X' X a).2
  · intro B B₀ aB _ _ _ aB₀ _ _ _ b hb d X X₀ sq
    obtain ⟨⟨κ, hκ, hδ⟩, _⟩ := section_constant_trivialization P aB X
    obtain ⟨⟨κ₀, hκ₀, hδ₀⟩, hfaith⟩ := section_constant_trivialization P aB₀ X₀
    let T := baseComparison P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB)
      ((AffineSpace (ULift.{u} (Fin 1)) B₀ ↘ B₀) ≫ aB₀) (familyBaseChange P aB aB₀ sq)
    have hread := constant_family_base_change P b _ _ _ _ κ κ₀ T
      (baseComparison P aB aB₀ sq) hfaith (by
        simpa only [← Iso.trans_assoc, hκ, hκ₀] using (hB B B₀ aB aB₀ b hb d X X₀ sq).1)
    rw [hδ, hδ₀, Functor.mapIso_trans, Functor.mapIso_symm]
    exact ratio_square _ _ _ _
      (endpointPull P b _ _ (AffineSpace.zeroSection_comp_map b)
          (invariant P ((AffineSpace (ULift.{u} (Fin 1)) B ↘ B) ≫ aB) (familyPair X)) ≪≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
          (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B₀)).leftDerivedFunctor.mapIso T)
      _ _ (by simpa only [Iso.trans_assoc] using hread.symm)
      (by simpa only [Iso.trans_assoc] using (hB B B₀ aB aB₀ b hb d X X₀ sq).2)
  · intro B aB _ _ _
    obtain ⟨⟨κ, hκ, hδ⟩, hfaith⟩ :=
      section_constant_trivialization P aB (standardZero B)
    obtain ⟨κ₀, h₁, h₀⟩ := rank_zero_family_readings P aB
    have he : κ = κ₀ := by
      apply hfaith
      have h := hκ.trans h₁.symm
      have h' := congrArg
        (fun e ↦ e ≪≫
          ((lineCounit P B _ (AffineSpace.oneSection_comp_over _ B)).app _).symm) h
      simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using h'
    rw [hδ, he, h₀]
    simp only [Iso.trans_symm, Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

end WeilConjectures.PurityFiniteSetting.SectionRestriction
