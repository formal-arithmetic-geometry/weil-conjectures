/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExternalIhom

/-! # Factoring the coefficient-dual tensor evaluation through internal Hom

Source: the generator calculation in sk-thm-sf-kunneth-verdier, step 1.
(blueprint: lem-sf-kv-hom-evaluation-factorization).
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace AlgebraicGeometry.ProEtale.CondensedRing.KVGenerator

/-- The counit evaluated on a specified adjunct recovers the original map.
Source: generator calculation, ordinary counit characterization
(blueprint: lem-sf-kv-hom-evaluation-factorization).
Proof: the adjunction's counit formula followed by the inverse-law of its Hom bijection. -/
theorem adjunct_counit {C D : Type*} [Category C] [Category D]
    {P : C ⥤ D} {R : D ⥤ C} (adj : P ⊣ R)
    {N : C} {T : D} (a : P.obj N ⟶ T) :
    P.map (adj.homEquiv N T a) ≫ adj.counit.app T = a := by
  exact (adj.homEquiv_counit (g := adj.homEquiv N T a)).symm.trans
    ((adj.homEquiv N T).symm_apply_apply a)

/-- Projection naturality and ordinary counit naturality identify the coefficient-dual
pairing with the internal-Hom exchange preceded by the dual-tensor comparison.
Source: sk-thm-sf-kunneth-verdier.proof.md, generator formula, step 1
(blueprint: lem-sf-kv-hom-evaluation-factorization).
Proof: uncurry the two sides. Move the pushforward of the dual-tensor comparison
through projection, then through the ordinary counit. Its composition with evaluation
is the defining uncurrying of the dual-tensor comparison. -/
theorem evaluation_comparison_factorization
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalCategory D] [MonoidalClosed D]
    (F : C ⥤ D) (P : D ⥤ C) (R : C ⥤ D) (adj : P ⊣ R)
    (pf : ∀ (K : C) (N : D), F.obj K ⊗ N ⟶ F.obj (K ⊗ P.obj N))
    (hpf : ∀ (K : C) {N N' : D} (b : N ⟶ N'),
      (F.obj K ◁ b) ≫ pf K N' = pf K N ≫ F.map (K ◁ P.map b))
    (K Q : C) (L : D) (c : F.obj Q ⟶ L) :
    curry (pf K _ ≫
      F.map ((K ◁ adj.counit.app _) ≫
        (α_ K ((ihom K).obj (𝟙_ C)) Q).inv ≫
        ((ihom.ev K).app (𝟙_ C) ▷ Q) ≫ (λ_ Q).hom) ≫ c) =
      R.map (ihomUnitTensorToIhom K Q) ≫
        curry (pf K _ ≫
          F.map ((K ◁ adj.counit.app _) ≫ (ihom.ev K).app Q) ≫ c) := by
  apply uncurry_injective
  rw [uncurry_curry, uncurry_natural_left, uncurry_curry]
  rw [reassoc_of% (hpf K (R.map (ihomUnitTensorToIhom K Q)))]
  have hn : P.map (R.map (ihomUnitTensorToIhom K Q)) ≫ adj.counit.app _ =
      adj.counit.app _ ≫ ihomUnitTensorToIhom K Q := by
    simpa only [Functor.comp_map, Functor.id_map] using
      adj.counit.naturality (ihomUnitTensorToIhom K Q)
  rw [← F.map_comp_assoc, ← whiskerLeft_comp_assoc, hn, whiskerLeft_comp_assoc,
    ← uncurry_eq, ihomUnitTensorToIhom, uncurry_curry]

/-- Naturality in the target of coefficient evaluation tensored with that target.
Source: generator calculation, step 4
(blueprint: lem-sf-kv-hom-evaluation-factorization).
Proof: associator naturality moves the map past reassociation, the interchange law
moves it past evaluation, and left-unitor naturality gives the result. -/
theorem unit_tensor_evaluation_natural
    {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]
    (K Q Q' : C) (a : Q ⟶ Q') :
    (K ◁ ((ihom K).obj (𝟙_ C) ◁ a)) ≫
        (α_ K ((ihom K).obj (𝟙_ C)) Q').inv ≫
        ((ihom.ev K).app (𝟙_ C) ▷ Q') ≫ (λ_ Q').hom =
      (α_ K ((ihom K).obj (𝟙_ C)) Q).inv ≫
        ((ihom.ev K).app (𝟙_ C) ▷ Q) ≫ (λ_ Q).hom ≫ a := by
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
  simp only [Functor.id_obj, leftUnitor_naturality]

/-- Normal form of the uncurried coefficient-dual comparison after an ordinary
adjunct and a map of the exceptional target.
Source: generator calculation, steps 3--4
(blueprint: lem-sf-kv-hom-evaluation-factorization).
Proof: uncurry and move the whole ordinary-input map through projection. Naturality
of the ordinary counit replaces P R of the shuffle by the shuffle after the counit.
Naturality of coefficient evaluation moves the target map outside evaluation. -/
theorem uncurry_comparison_word
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalCategory D] [MonoidalClosed D]
    (F : C ⥤ D) (P : D ⥤ C) (R : C ⥤ D) (adj : P ⊣ R)
    (pf : ∀ (K : C) (N : D), F.obj K ⊗ N ⟶ F.obj (K ⊗ P.obj N))
    (hpf : ∀ (K : C) {N N' : D} (b : N ⟶ N'),
      (F.obj K ◁ b) ≫ pf K N' = pf K N ≫ F.map (K ◁ P.map b))
    (K Q Q' : C) (L N : D) (T : C) (o : N ⟶ R.obj T)
    (s : T ⟶ (ihom K).obj (𝟙_ C) ⊗ Q) (a : Q ⟶ Q') (c : F.obj Q' ⟶ L) :
    uncurry (o ≫ R.map (s ≫ ((ihom K).obj (𝟙_ C) ◁ a)) ≫
      curry (pf K _ ≫
        F.map ((K ◁ adj.counit.app _) ≫
          (α_ K ((ihom K).obj (𝟙_ C)) Q').inv ≫
          ((ihom.ev K).app (𝟙_ C) ▷ Q') ≫ (λ_ Q').hom) ≫ c)) =
      pf K N ≫
        F.map ((K ◁ (P.map o ≫ adj.counit.app T ≫ s)) ≫
          (α_ K ((ihom K).obj (𝟙_ C)) Q).inv ≫
          ((ihom.ev K).app (𝟙_ C) ▷ Q) ≫ (λ_ Q).hom) ≫ F.map a ≫ c := by
  rw [← Category.assoc o, uncurry_natural_left, uncurry_curry,
    reassoc_of% (hpf K (o ≫ R.map (s ≫ ((ihom K).obj (𝟙_ C) ◁ a))))]
  have hn : P.map (o ≫ R.map (s ≫ ((ihom K).obj (𝟙_ C) ◁ a))) ≫
      adj.counit.app _ = P.map o ≫ adj.counit.app T ≫
        s ≫ ((ihom K).obj (𝟙_ C) ◁ a) := by
    rw [P.map_comp, Category.assoc]
    have hnat := adj.counit.naturality (s ≫ ((ihom K).obj (𝟙_ C) ◁ a))
    simp only [Functor.comp_map, Functor.id_map] at hnat
    rw [hnat]
  rw [← F.map_comp_assoc, ← whiskerLeft_comp_assoc, hn]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [unit_tensor_evaluation_natural]
  simp only [F.map_comp, Category.assoc]

/-- Uncurrying the external Hom map after a pair of input comparisons gives the
external product of their actual uncurried evaluations.
Source: generator calculation, step 5
(blueprint: lem-sf-kv-hom-evaluation-factorization).
Proof: uncurry input composition, move its two factors through middle-four
interchange, and then through the two monoidal tensor comparisons. Functoriality
identifies the resulting evaluation composites with their uncurrying. -/
theorem uncurry_external_after
    {C D₁ D₂ : Type*} [Category C] [Category D₁] [Category D₂]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
    [MonoidalCategory D₁] [MonoidalClosed D₁]
    [MonoidalCategory D₂] [MonoidalClosed D₂]
    (F₁ : D₁ ⥤ C) (F₂ : D₂ ⥤ C) [F₁.LaxMonoidal] [F₂.LaxMonoidal]
    (E₁ N₁ L₁ : D₁) (E₂ N₂ L₂ : D₂)
    (h₁ : N₁ ⟶ (ihom E₁).obj L₁) (h₂ : N₂ ⟶ (ihom E₂).obj L₂) :
    uncurry ((F₁.map h₁ ⊗ₘ F₂.map h₂) ≫
      externalIhomMap F₁ F₂ E₁ L₁ E₂ L₂) =
    tensorμ _ _ _ _ ≫
      ((Functor.LaxMonoidal.μ F₁ E₁ N₁ ≫ F₁.map (uncurry h₁)) ⊗ₘ
        (Functor.LaxMonoidal.μ F₂ E₂ N₂ ≫ F₂.map (uncurry h₂))) := by
  rw [uncurry_natural_left, uncurry_externalIhomMap, tensorμ_natural_right_assoc,
    tensorHom_comp_tensorHom]
  simp only [Functor.LaxMonoidal.μ_natural_right_assoc,
    ← F₁.map_comp, ← F₂.map_comp, ← uncurry_eq]

end AlgebraicGeometry.ProEtale.CondensedRing.KVGenerator
