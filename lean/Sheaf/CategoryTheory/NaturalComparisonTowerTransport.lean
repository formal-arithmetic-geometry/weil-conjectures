/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Sheaf.CategoryTheory.ScalarLocalization
public import Sheaf.CategoryTheory.SemilinearScalarLocalization

/-!
# Transport of twist towers through specified natural comparisons

Source: Weil conjectures blueprint, `sec-six-functors-basics/sk-prop-sf-existence`,
`prop-weil-twist-preserves.proof.md`, final common-stage sentence
(blueprint: lem-weil-natural-comparison-tower-transport).

The declarations separate the purely categorical tower, its identity transitions,
and the scalar-localization calculus applicable to every comparison in that tower.
All constructions use the given comparisons, including their inverse components.
-/

@[expose] public section

universe u₀ v₀ u₁ v₁ u₂ v₂ r s q

namespace CategoryTheory.NaturalComparisonTowerTransport

variable {C₀ : Type u₀} [Category.{v₀} C₀]
  {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]

/-- The specified two-step comparison d, inner comparison first.
Source: blueprint, final common-stage sentence, node Step 1
(blueprint: lem-weil-natural-comparison-tower-transport). -/
def comparison {T₁₀ B₁₀ : C₀ ⥤ C₁} {T₂₁ B₂₁ : C₁ ⥤ C₂}
    (χ₁₀ : T₁₀ ≅ B₁₀) (χ₂₁ : T₂₁ ≅ B₂₁) :
    T₁₀ ⋙ T₂₁ ≅ B₁₀ ⋙ B₂₁ :=
  Functor.isoWhiskerRight χ₁₀ T₂₁ ≪≫ Functor.isoWhiskerLeft B₁₀ χ₂₁

/-- The transported associator a = chi20 mu d inverse.
Source: blueprint, final common-stage sentence, node Step 1
(blueprint: lem-weil-natural-comparison-tower-transport). -/
def associator {T₁₀ B₁₀ : C₀ ⥤ C₁} {T₂₁ B₂₁ : C₁ ⥤ C₂} {T₂₀ B₂₀ : C₀ ⥤ C₂}
    (χ₁₀ : T₁₀ ≅ B₁₀) (χ₂₁ : T₂₁ ≅ B₂₁) (χ₂₀ : T₂₀ ≅ B₂₀)
    (μ : T₁₀ ⋙ T₂₁ ≅ T₂₀) : B₁₀ ⋙ B₂₁ ≅ B₂₀ :=
  (comparison χ₁₀ χ₂₁).symm ≪≫ μ ≪≫ χ₂₀

/-- Conjugate a twist comparison by the specified chi.
Source: blueprint, final common-stage sentence, node Step 1
(blueprint: lem-weil-natural-comparison-tower-transport). -/
def twist {T B : C₀ ⥤ C₁} (χ : T ≅ B) (W₀ : C₀ ⥤ C₀) (W₁ : C₁ ⥤ C₁)
    (α : W₀ ⋙ T ≅ T ⋙ W₁) : W₀ ⋙ B ≅ B ⋙ W₁ :=
  Functor.isoWhiskerLeft W₀ χ.symm ≪≫ α ≪≫ Functor.isoWhiskerRight χ W₁

/-- The actual transported unit, with no strict identity-transition convention.
Source: blueprint, final common-stage sentence, node Steps 1 and 4
(blueprint: lem-weil-natural-comparison-tower-transport). -/
def unitIso {T B : C₀ ⥤ C₀} (χ : T ≅ B) (u : T ≅ 𝟭 C₀) : B ≅ 𝟭 C₀ :=
  χ.symm ≪≫ u

/-- The transported tower equation and its two specified path normalizations.
Source: blueprint, final common-stage sentence, displayed equations
(blueprint: lem-weil-natural-comparison-tower-transport). -/
def TowerEquations
    {T₁₀ B₁₀ : C₀ ⥤ C₁} {T₂₁ B₂₁ : C₁ ⥤ C₂} {T₂₀ B₂₀ : C₀ ⥤ C₂}
    (χ₁₀ : T₁₀ ≅ B₁₀) (χ₂₁ : T₂₁ ≅ B₂₁) (χ₂₀ : T₂₀ ≅ B₂₀)
    (W₀ : C₀ ⥤ C₀) (W₁ : C₁ ⥤ C₁) (W₂ : C₂ ⥤ C₂)
    (α₁₀ : W₀ ⋙ T₁₀ ≅ T₁₀ ⋙ W₁) (α₂₁ : W₁ ⋙ T₂₁ ≅ T₂₁ ⋙ W₂)
    (α₂₀ : W₀ ⋙ T₂₀ ≅ T₂₀ ⋙ W₂) (μ : T₁₀ ⋙ T₂₁ ≅ T₂₀) : Prop :=
    (∀ K : C₀,
      B₂₁.map ((twist χ₁₀ W₀ W₁ α₁₀).hom.app K) ≫
          (twist χ₂₁ W₁ W₂ α₂₁).hom.app (B₁₀.obj K) ≫
          W₂.map ((associator χ₁₀ χ₂₁ χ₂₀ μ).hom.app K) =
        (associator χ₁₀ χ₂₁ χ₂₀ μ).hom.app (W₀.obj K) ≫
          (twist χ₂₀ W₀ W₂ α₂₀).hom.app K) ∧
    (∀ K : C₀,
      (comparison χ₁₀ χ₂₁).hom.app (W₀.obj K) ≫
          B₂₁.map ((twist χ₁₀ W₀ W₁ α₁₀).hom.app K) ≫
          (twist χ₂₁ W₁ W₂ α₂₁).hom.app (B₁₀.obj K) =
        T₂₁.map (α₁₀.hom.app K) ≫ α₂₁.hom.app (T₁₀.obj K) ≫
          W₂.map ((comparison χ₁₀ χ₂₁).hom.app K)) ∧
    (∀ K : C₀,
      (comparison χ₁₀ χ₂₁).hom.app (W₀.obj K) ≫
          (associator χ₁₀ χ₂₁ χ₂₀ μ).hom.app (W₀.obj K) ≫
          (twist χ₂₀ W₀ W₂ α₂₀).hom.app K =
        μ.hom.app (W₀.obj K) ≫ α₂₀.hom.app K ≫ W₂.map (χ₂₀.hom.app K))

/-- The transported tower equation and both path normalizations.
Source: blueprint, final common-stage sentence
(blueprint: lem-weil-natural-comparison-tower-transport).
Proof (node Steps 1--3): the definitions are composites and whiskerings of natural
isomorphisms, hence are natural with the displayed inverses. For the first normalization,
naturality of chi21 at beta10 moves B21(beta10) across chi21 inverse. Expand beta10
and cancel T21(chi10 inverse) T21(chi10). Naturality of alpha21 at chi10 then gives
W2(d) alpha21 T21(alpha10). For the second normalization expand beta20 and a and
cancel chi20 inverse chi20 and d inverse d. Precompose both transported tower paths
by the invertible d at W0(K). The two normalizations reduce their equality to the
assumed ordinary tower equation, after applying W2(chi20). Cancel d.
-/
theorem tower
    {T₁₀ B₁₀ : C₀ ⥤ C₁} {T₂₁ B₂₁ : C₁ ⥤ C₂} {T₂₀ B₂₀ : C₀ ⥤ C₂}
    (χ₁₀ : T₁₀ ≅ B₁₀) (χ₂₁ : T₂₁ ≅ B₂₁) (χ₂₀ : T₂₀ ≅ B₂₀)
    (W₀ : C₀ ⥤ C₀) (W₁ : C₁ ⥤ C₁) (W₂ : C₂ ⥤ C₂)
    (α₁₀ : W₀ ⋙ T₁₀ ≅ T₁₀ ⋙ W₁) (α₂₁ : W₁ ⋙ T₂₁ ≅ T₂₁ ⋙ W₂)
    (α₂₀ : W₀ ⋙ T₂₀ ≅ T₂₀ ⋙ W₂) (μ : T₁₀ ⋙ T₂₁ ≅ T₂₀)
    (h : ∀ K : C₀,
      T₂₁.map (α₁₀.hom.app K) ≫ α₂₁.hom.app (T₁₀.obj K) ≫ W₂.map (μ.hom.app K) =
        μ.hom.app (W₀.obj K) ≫ α₂₀.hom.app K) :
    TowerEquations χ₁₀ χ₂₁ χ₂₀ W₀ W₁ W₂ α₁₀ α₂₁ α₂₀ μ := by
  sorry

/-- Unit compatibility survives conjugation, for any identity transition.
Source: blueprint, final common-stage sentence
(blueprint: lem-weil-natural-comparison-tower-transport).
Proof (node Step 4): expand v and beta. Functoriality cancels W(chi inverse) W(chi),
and the hypothesis changes W(u) alpha to u at W(K). The remaining composite is
chi inverse at W(K) followed by u at W(K), exactly v at W(K).
-/
theorem unit {T B : C₀ ⥤ C₀} (χ : T ≅ B) (u : T ≅ 𝟭 C₀)
    (W : C₀ ⥤ C₀) (α : W ⋙ T ≅ T ⋙ W)
    (h : ∀ K : C₀, α.hom.app K ≫ W.map (u.hom.app K) = u.hom.app (W.obj K)) :
    ∀ K : C₀, (twist χ W W α).hom.app K ≫ W.map ((unitIso χ u).hom.app K) =
      (unitIso χ u).hom.app (W.obj K) := by
  sorry

/-- Both repeated-index associators are the whiskered actual transported units.
This includes the fully repeated case by specializing the two categories and transitions.
Source: blueprint, final common-stage sentence
(blueprint: lem-weil-natural-comparison-tower-transport).
Proof (node Step 5): for the source repetition expand a with mu = Tji(ui).
Cancel the inner comparison and use naturality of chiji at vi to obtain Bji(vi).
For the target repetition expand a with mu = uj Tji and use naturality of uj at
chiji to obtain vj at Bji(K). These calculations need no pentagon assumption.
-/
theorem unit_degeneracies {T B : C₀ ⥤ C₁} (χ : T ≅ B)
    {T₀ B₀ : C₀ ⥤ C₀} {T₁ B₁ : C₁ ⥤ C₁}
    (χ₀ : T₀ ≅ B₀) (χ₁ : T₁ ≅ B₁) (u₀ : T₀ ≅ 𝟭 C₀) (u₁ : T₁ ≅ 𝟭 C₁) :
    (∀ K : C₀,
      (associator χ₀ χ χ
        (Functor.isoWhiskerRight u₀ T ≪≫ Functor.leftUnitor T)).hom.app K =
          B.map ((unitIso χ₀ u₀).hom.app K)) ∧
    (∀ K : C₀,
      (associator χ χ₁ χ
        (Functor.isoWhiskerLeft T u₁ ≪≫ Functor.rightUnitor T)).hom.app K =
          (unitIso χ₁ u₁).hom.app (B.obj K)) := by
  sorry

section ScalarExtension

open ScalarLocalization TensorProduct

variable {R : Type r} [CommRing R] {S : Type s} [CommRing S]
  [Preadditive C₀] [Linear R C₀] [Preadditive C₁] [Linear S C₁]
  (t : R) (b : S) (φ : R →+* S)
  (hφ : IsUnit (algebraMap S (Localization.Away b) (φ t)))

/-- Every comparison and its inverse extend naturally on the full raw localization;
the formula includes pure tensors, finite sums and transport through specified comparisons.
Source: blueprint, final common-stage sentence and scalar-extension composition
(blueprint: lem-weil-natural-comparison-tower-transport).
Proof (node Steps 6--7): apply lem-pur-semilinear-scalar-localization to the additive
semilinear functors. Its component prescription gives Q(eta) and Q(eta inverse).
On a pure tensor s tensor f the functor maps are barphi(s) tensor F(f); integral
naturality and bilinear composition move this common scalar through Q(eta).
Additivity gives the same equality for every finite sum, hence every tensor-Hom arrow.
Functoriality gives both inverse equations, and preservation of vertical composition
and inverse components identifies localized a with localized chi mu d inverse.
No cancellation by Q and no faithfulness assertion occurs.
-/
theorem localized_comparisons
    {F G H J : C₀ ⥤ C₁} [F.Additive] [G.Additive] [H.Additive] [J.Additive]
    (hF : IsSemilinear φ F) (hG : IsSemilinear φ G)
    (hH : IsSemilinear φ H) (hJ : IsSemilinear φ J)
    (d : F ≅ G) (μ : F ≅ H) (χ : H ≅ J) :
    ∃ (dbar : extension t b φ hφ F hF ≅ extension t b φ hφ G hG)
      (μbar : extension t b φ hφ F hF ≅ extension t b φ hφ H hH)
      (χbar : extension t b φ hφ H hH ≅ extension t b φ hφ J hJ)
      (abar : extension t b φ hφ G hG ≅ extension t b φ hφ J hJ),
    (∀ K : C₀,
      dbar.hom.app ⟨K⟩ =
        (localization S C₁ b).map (d.hom.app K) ∧
      dbar.inv.app ⟨K⟩ =
        (localization S C₁ b).map (d.inv.app K)) ∧
    (∀ K : C₀,
      μbar.hom.app ⟨K⟩ =
        (localization S C₁ b).map (μ.hom.app K) ∧
      μbar.inv.app ⟨K⟩ =
        (localization S C₁ b).map (μ.inv.app K)) ∧
    (∀ K : C₀,
      χbar.hom.app ⟨K⟩ =
        (localization S C₁ b).map (χ.hom.app K) ∧
      χbar.inv.app ⟨K⟩ =
        (localization S C₁ b).map (χ.inv.app K)) ∧
    (∀ K : C₀,
      abar.hom.app ⟨K⟩ =
        (localization S C₁ b).map ((d.symm ≪≫ μ ≪≫ χ).hom.app K) ∧
      abar.inv.app ⟨K⟩ =
        (localization S C₁ b).map ((d.symm ≪≫ μ ≪≫ χ).inv.app K)) ∧
    (∀ (K L : C₀) (f : K ⟶ L) (a : Localization.Away t),
      (extension t b φ hφ F hF).map
          (a ⊗ₜ[R] f : ScalarLocalization.mk K ⟶ ScalarLocalization.mk L) =
        coefficientMap t b φ hφ a ⊗ₜ[S] F.map f) ∧
    (∀ (K L : ScalarLocalization R C₀ t) (f : K ⟶ L),
      (extension t b φ hφ F hF).map f ≫
          dbar.hom.app L =
        dbar.hom.app K ≫
          (extension t b φ hφ G hG).map f) ∧
    (∀ (K L : ScalarLocalization R C₀ t) (f : K ⟶ L),
      (extension t b φ hφ G hG).map f ≫
          dbar.inv.app L =
        dbar.inv.app K ≫
          (extension t b φ hφ F hF).map f) ∧
    (∀ K : ScalarLocalization R C₀ t,
      dbar.hom.app K ≫
          dbar.inv.app K =
        𝟙 ((extension t b φ hφ F hF).obj K) ∧
      dbar.inv.app K ≫
          dbar.hom.app K =
        𝟙 ((extension t b φ hφ G hG).obj K)) ∧
    abar =
      dbar.symm ≪≫
        μbar ≪≫ χbar := by
  sorry

end ScalarExtension

section LocalizedTower

open ScalarLocalization

variable {R₀ : Type r} [CommRing R₀] {R₁ : Type s} [CommRing R₁]
  {R₂ : Type q} [CommRing R₂]
  [Preadditive C₀] [Linear R₀ C₀] [Preadditive C₁] [Linear R₁ C₁]
  [Preadditive C₂] [Linear R₂ C₂]
  (t₀ : R₀) (t₁ : R₁) (t₂ : R₂) (φ₁₀ : R₀ →+* R₁) (φ₂₁ : R₁ →+* R₂)
  (h₁₀ : IsUnit (algebraMap R₁ (Localization.Away t₁) (φ₁₀ t₀)))
  (h₂₁ : IsUnit (algebraMap R₂ (Localization.Away t₂) (φ₂₁ t₁)))
  (h₂₀ : IsUnit (algebraMap R₂ (Localization.Away t₂) ((φ₂₁.comp φ₁₀) t₀)))
  {T₁₀ B₁₀ : C₀ ⥤ C₁} {T₂₁ B₂₁ : C₁ ⥤ C₂} {T₂₀ B₂₀ : C₀ ⥤ C₂}
  [T₁₀.Additive] [B₁₀.Additive] [T₂₁.Additive] [B₂₁.Additive]
  [T₂₀.Additive] [B₂₀.Additive]
  (hT₁₀ : IsSemilinear φ₁₀ T₁₀) (hB₁₀ : IsSemilinear φ₁₀ B₁₀)
  (hT₂₁ : IsSemilinear φ₂₁ T₂₁) (hB₂₁ : IsSemilinear φ₂₁ B₂₁)
  (hT₂₀ : IsSemilinear (φ₂₁.comp φ₁₀) T₂₀)
  (hB₂₀ : IsSemilinear (φ₂₁.comp φ₁₀) B₂₀)
  (χ₁₀ : T₁₀ ≅ B₁₀) (χ₂₁ : T₂₁ ≅ B₂₁) (χ₂₀ : T₂₀ ≅ B₂₀)
  (W₀ : C₀ ⥤ C₀) (W₁ : C₁ ⥤ C₁) (W₂ : C₂ ⥤ C₂)
  [W₀.Additive] [W₁.Additive] [W₂.Additive]
  [W₀.Linear R₀] [W₁.Linear R₁] [W₂.Linear R₂]
  (α₁₀ : W₀ ⋙ T₁₀ ≅ T₁₀ ⋙ W₁) (α₂₁ : W₁ ⋙ T₂₁ ≅ T₂₁ ⋙ W₂)
  (α₂₀ : W₀ ⋙ T₂₀ ≅ T₂₀ ⋙ W₂) (μ : T₁₀ ⋙ T₂₁ ≅ T₂₀)

/-- The tower, both path normalizations and their canonical components after localization.
The witnesses are natural isomorphisms on the raw tensor-Hom categories, so their
naturality includes every localized arrow. Their components and inverses are prescribed,
not arbitrary choices of comparison maps.
Source: blueprint, final common-stage sentence and scalar-extension composition
(blueprint: lem-weil-natural-comparison-tower-transport).
Proof (node Steps 6--7): extend T and B using lem-pur-semilinear-scalar-localization,
and use its identity-coefficient case for the linear W. Extend alpha and mu and identify
the composite endpoints by its composition and linear-endofunctor equations. Components
and inverse components are Q of the original ones. The lemma preserves whiskering,
vertical composition and inverse equations; hence localized d, a and beta have precisely
the Q-components below. Apply Q to the ordinary tower, then use these component formulas
and integral agreement of the extended functors. This gives the localized ordinary tower;
apply tower to obtain all three transported equations. On pure tensors naturality is
integral naturality times the coefficient image; tensor additivity extends it to all arrows.
-/
theorem localized_tower
    (h : ∀ K : C₀,
      T₂₁.map (α₁₀.hom.app K) ≫ α₂₁.hom.app (T₁₀.obj K) ≫ W₂.map (μ.hom.app K) =
        μ.hom.app (W₀.obj K) ≫ α₂₀.hom.app K) :
    ∃ (χ₁₀bar : extension t₀ t₁ φ₁₀ h₁₀ T₁₀ hT₁₀ ≅
        extension t₀ t₁ φ₁₀ h₁₀ B₁₀ hB₁₀)
      (χ₂₁bar : extension t₁ t₂ φ₂₁ h₂₁ T₂₁ hT₂₁ ≅
        extension t₁ t₂ φ₂₁ h₂₁ B₂₁ hB₂₁)
      (χ₂₀bar : extension t₀ t₂ (φ₂₁.comp φ₁₀) h₂₀ T₂₀ hT₂₀ ≅
        extension t₀ t₂ (φ₂₁.comp φ₁₀) h₂₀ B₂₀ hB₂₀)
      (α₁₀bar :
      (ScalarLocalization.map R₀ C₀ t₀ W₀) ⋙
        (extension t₀ t₁ φ₁₀ h₁₀ T₁₀ hT₁₀) ≅
      (extension t₀ t₁ φ₁₀ h₁₀ T₁₀ hT₁₀) ⋙
        (ScalarLocalization.map R₁ C₁ t₁ W₁))
      (α₂₁bar :
      (ScalarLocalization.map R₁ C₁ t₁ W₁) ⋙
        (extension t₁ t₂ φ₂₁ h₂₁ T₂₁ hT₂₁) ≅
      (extension t₁ t₂ φ₂₁ h₂₁ T₂₁ hT₂₁) ⋙
        (ScalarLocalization.map R₂ C₂ t₂ W₂))
      (α₂₀bar :
      (ScalarLocalization.map R₀ C₀ t₀ W₀) ⋙
        (extension t₀ t₂ (φ₂₁.comp φ₁₀) h₂₀ T₂₀ hT₂₀) ≅
      (extension t₀ t₂ (φ₂₁.comp φ₁₀) h₂₀ T₂₀ hT₂₀) ⋙
        (ScalarLocalization.map R₂ C₂ t₂ W₂))
      (μbar :
        (extension t₀ t₁ φ₁₀ h₁₀ T₁₀ hT₁₀) ⋙
          (extension t₁ t₂ φ₂₁ h₂₁ T₂₁ hT₂₁) ≅
        (extension t₀ t₂ (φ₂₁.comp φ₁₀) h₂₀ T₂₀ hT₂₀)),
      (∀ K : C₀,
        χ₁₀bar.hom.app ⟨K⟩ = (localization R₁ C₁ t₁).map (χ₁₀.hom.app K) ∧
        χ₁₀bar.inv.app ⟨K⟩ = (localization R₁ C₁ t₁).map (χ₁₀.inv.app K)) ∧
      (∀ K : C₁,
        χ₂₁bar.hom.app ⟨K⟩ = (localization R₂ C₂ t₂).map (χ₂₁.hom.app K) ∧
        χ₂₁bar.inv.app ⟨K⟩ = (localization R₂ C₂ t₂).map (χ₂₁.inv.app K)) ∧
      (∀ K : C₀,
        χ₂₀bar.hom.app ⟨K⟩ = (localization R₂ C₂ t₂).map (χ₂₀.hom.app K) ∧
        χ₂₀bar.inv.app ⟨K⟩ = (localization R₂ C₂ t₂).map (χ₂₀.inv.app K)) ∧
      (∀ K : C₀,
        α₁₀bar.hom.app ⟨K⟩ = (localization R₁ C₁ t₁).map (α₁₀.hom.app K) ∧
        α₁₀bar.inv.app ⟨K⟩ = (localization R₁ C₁ t₁).map (α₁₀.inv.app K)) ∧
      (∀ K : C₁,
        α₂₁bar.hom.app ⟨K⟩ = (localization R₂ C₂ t₂).map (α₂₁.hom.app K) ∧
        α₂₁bar.inv.app ⟨K⟩ = (localization R₂ C₂ t₂).map (α₂₁.inv.app K)) ∧
      (∀ K : C₀,
        α₂₀bar.hom.app ⟨K⟩ = (localization R₂ C₂ t₂).map (α₂₀.hom.app K) ∧
        α₂₀bar.inv.app ⟨K⟩ = (localization R₂ C₂ t₂).map (α₂₀.inv.app K)) ∧
      (∀ K : C₀,
        μbar.hom.app ⟨K⟩ = (localization R₂ C₂ t₂).map (μ.hom.app K) ∧
        μbar.inv.app ⟨K⟩ = (localization R₂ C₂ t₂).map (μ.inv.app K)) ∧
      (∀ K : ScalarLocalization R₀ C₀ t₀,
        (extension t₁ t₂ φ₂₁ h₂₁ T₂₁ hT₂₁).map (α₁₀bar.hom.app K) ≫
            α₂₁bar.hom.app ((extension t₀ t₁ φ₁₀ h₁₀ T₁₀ hT₁₀).obj K) ≫
            (ScalarLocalization.map R₂ C₂ t₂ W₂).map (μbar.hom.app K) =
          μbar.hom.app ((ScalarLocalization.map R₀ C₀ t₀ W₀).obj K) ≫
            α₂₀bar.hom.app K) ∧
      TowerEquations
        χ₁₀bar
        χ₂₁bar
        χ₂₀bar
        (ScalarLocalization.map R₀ C₀ t₀ W₀)
        (ScalarLocalization.map R₁ C₁ t₁ W₁)
        (ScalarLocalization.map R₂ C₂ t₂ W₂)
        α₁₀bar α₂₁bar α₂₀bar μbar ∧
      (∀ K : C₀,
        (comparison
          χ₁₀bar
          χ₂₁bar).hom.app ⟨K⟩ =
            (localization R₂ C₂ t₂).map ((comparison χ₁₀ χ₂₁).hom.app K) ∧
        (comparison
          χ₁₀bar
          χ₂₁bar).inv.app ⟨K⟩ =
            (localization R₂ C₂ t₂).map ((comparison χ₁₀ χ₂₁).inv.app K)) ∧
      (∀ K : C₀,
        (associator
          χ₁₀bar
          χ₂₁bar
          χ₂₀bar μbar).hom.app ⟨K⟩ =
            (localization R₂ C₂ t₂).map ((associator χ₁₀ χ₂₁ χ₂₀ μ).hom.app K) ∧
        (associator
          χ₁₀bar
          χ₂₁bar
          χ₂₀bar μbar).inv.app ⟨K⟩ =
            (localization R₂ C₂ t₂).map ((associator χ₁₀ χ₂₁ χ₂₀ μ).inv.app K)) ∧
      (∀ K : C₀,
        (twist
          χ₁₀bar
          (ScalarLocalization.map R₀ C₀ t₀ W₀)
          (ScalarLocalization.map R₁ C₁ t₁ W₁) α₁₀bar).hom.app ⟨K⟩ =
            (localization R₁ C₁ t₁).map ((twist χ₁₀ W₀ W₁ α₁₀).hom.app K) ∧
        (twist
          χ₁₀bar
          (ScalarLocalization.map R₀ C₀ t₀ W₀)
          (ScalarLocalization.map R₁ C₁ t₁ W₁) α₁₀bar).inv.app ⟨K⟩ =
            (localization R₁ C₁ t₁).map ((twist χ₁₀ W₀ W₁ α₁₀).inv.app K)) ∧
      (∀ K : C₁,
        (twist
          χ₂₁bar
          (ScalarLocalization.map R₁ C₁ t₁ W₁)
          (ScalarLocalization.map R₂ C₂ t₂ W₂) α₂₁bar).hom.app ⟨K⟩ =
            (localization R₂ C₂ t₂).map ((twist χ₂₁ W₁ W₂ α₂₁).hom.app K) ∧
        (twist
          χ₂₁bar
          (ScalarLocalization.map R₁ C₁ t₁ W₁)
          (ScalarLocalization.map R₂ C₂ t₂ W₂) α₂₁bar).inv.app ⟨K⟩ =
            (localization R₂ C₂ t₂).map ((twist χ₂₁ W₁ W₂ α₂₁).inv.app K)) ∧
      (∀ K : C₀,
        (twist
          χ₂₀bar
          (ScalarLocalization.map R₀ C₀ t₀ W₀)
          (ScalarLocalization.map R₂ C₂ t₂ W₂) α₂₀bar).hom.app ⟨K⟩ =
            (localization R₂ C₂ t₂).map ((twist χ₂₀ W₀ W₂ α₂₀).hom.app K) ∧
        (twist
          χ₂₀bar
          (ScalarLocalization.map R₀ C₀ t₀ W₀)
          (ScalarLocalization.map R₂ C₂ t₂ W₂) α₂₀bar).inv.app ⟨K⟩ =
            (localization R₂ C₂ t₂).map ((twist χ₂₀ W₀ W₂ α₂₀).inv.app K)) := by
  sorry

end LocalizedTower

section LocalizedUnit

open ScalarLocalization

variable {R : Type r} [CommRing R] [Preadditive C₀] [Linear R C₀]

/-- The unit and its twist equation localize with their prescribed components and inverses.
The two repeated-index equations are then `unit_degeneracies` in the localized categories,
with these actual units, for any localized transition (including a self-transition).
Source: blueprint, final common-stage sentence and scalar-extension composition
(blueprint: lem-weil-natural-comparison-tower-transport).
Proof (node Steps 4--7): extend the linear identity-transition functors, W, chi, alpha
and u by lem-pur-semilinear-scalar-localization with the identity coefficient map.
Its identity and linear-functor equations identify the functors with ScalarLocalization.map
and identify the localized identity with the identity functor. Every component, including
inverse components, is Q of the original component. Map the assumed ordinary unit equation
by Q and use integral agreement of the extended W, giving the ordinary localized unit
compatibility. Apply unit to this equation. Expanding unitIso and twist and using that Q
preserves composition gives the two component and inverse-component formulas. Finally,
unit_degeneracies applied to these localizations gives both repeated-index associators;
naturality in the full raw category follows on pure tensors and then sums as in Step 7.
-/
theorem localized_unit (t : R) {T B : C₀ ⥤ C₀}
    [T.Additive] [B.Additive] [T.Linear R] [B.Linear R]
    (χ : T ≅ B) (u : T ≅ 𝟭 C₀) (W : C₀ ⥤ C₀) [W.Additive] [W.Linear R]
    (α : W ⋙ T ≅ T ⋙ W)
    (h : ∀ K : C₀, α.hom.app K ≫ W.map (u.hom.app K) = u.hom.app (W.obj K)) :
    ∃ (χbar : ScalarLocalization.map R C₀ t T ≅ ScalarLocalization.map R C₀ t B)
      (ubar : ScalarLocalization.map R C₀ t T ≅ 𝟭 (ScalarLocalization R C₀ t))
      (αbar : ScalarLocalization.map R C₀ t W ⋙ ScalarLocalization.map R C₀ t T ≅
        ScalarLocalization.map R C₀ t T ⋙ ScalarLocalization.map R C₀ t W),
      (∀ K : C₀,
        χbar.hom.app ⟨K⟩ = (localization R C₀ t).map (χ.hom.app K) ∧
        χbar.inv.app ⟨K⟩ = (localization R C₀ t).map (χ.inv.app K) ∧
        ubar.hom.app ⟨K⟩ = (localization R C₀ t).map (u.hom.app K) ∧
        ubar.inv.app ⟨K⟩ = (localization R C₀ t).map (u.inv.app K) ∧
        αbar.hom.app ⟨K⟩ = (localization R C₀ t).map (α.hom.app K) ∧
        αbar.inv.app ⟨K⟩ = (localization R C₀ t).map (α.inv.app K)) ∧
      (∀ K : ScalarLocalization R C₀ t,
        αbar.hom.app K ≫ (ScalarLocalization.map R C₀ t W).map (ubar.hom.app K) =
          ubar.hom.app ((ScalarLocalization.map R C₀ t W).obj K)) ∧
      (∀ K : ScalarLocalization R C₀ t,
        (twist χbar (ScalarLocalization.map R C₀ t W)
            (ScalarLocalization.map R C₀ t W) αbar).hom.app K ≫
            (ScalarLocalization.map R C₀ t W).map ((unitIso χbar ubar).hom.app K) =
          (unitIso χbar ubar).hom.app ((ScalarLocalization.map R C₀ t W).obj K)) ∧
      (∀ K : C₀,
        (unitIso χbar ubar).hom.app ⟨K⟩ =
          (localization R C₀ t).map ((unitIso χ u).hom.app K) ∧
        (unitIso χbar ubar).inv.app ⟨K⟩ =
          (localization R C₀ t).map ((unitIso χ u).inv.app K)) ∧
      (∀ K : C₀,
        (twist χbar (ScalarLocalization.map R C₀ t W)
            (ScalarLocalization.map R C₀ t W) αbar).hom.app ⟨K⟩ =
          (localization R C₀ t).map ((twist χ W W α).hom.app K) ∧
        (twist χbar (ScalarLocalization.map R C₀ t W)
            (ScalarLocalization.map R C₀ t W) αbar).inv.app ⟨K⟩ =
          (localization R C₀ t).map ((twist χ W W α).inv.app K)) := by
  sorry

end LocalizedUnit

end CategoryTheory.NaturalComparisonTowerTransport
