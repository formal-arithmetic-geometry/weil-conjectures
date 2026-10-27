/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # Coherence of evaluation transposes under strong symmetric monoidal functors

Source: literature/blueprint/master/blueprint/sec-six-functors/
sk-prop-sf-biduality-general/thm-coef-finite-hom.md, proof final paragraph
(blueprint: lem-coef-evaluation-transpose-coherence).

Mathlib's evaluation has source `K ⊗ H(K,M)`. The source's evaluation on
`H(K,M) ⊗ K` is therefore the symmetry followed by `ihom.ev`. Likewise its transpose
of `a : T ⊗ K ⟶ M` is `curry ((β_ K T).hom ≫ a)`, and its composition on
`H(M,N) ⊗ H(K,M)` is the symmetry followed by `MonoidalClosed.comp K M N`.
The comparison is the existing `Functor.LaxMonoidal.ihomComparison`, not a new map.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC uD vD uE vE

open CategoryTheory MonoidalCategory MonoidalClosed
open CategoryTheory.Functor.LaxMonoidal

namespace CategoryTheory.Functor.Braided

private theorem comparison_curry
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [MonoidalClosed C]
    {D : Type uD} [Category.{vD} D] [MonoidalCategory D] [MonoidalClosed D]
    (F : C ⥤ D) [F.LaxMonoidal] {K T M : C} (a : K ⊗ T ⟶ M) :
    F.map (curry a) ≫ (ihomComparison F K).natTrans.app M =
      curry (μ F K T ≫ F.map a) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_eq, ihomComparison_ev, μ_natural_right_assoc,
    ← F.map_comp, whiskerLeft_curry_ihom_ev_app, uncurry_curry]

private theorem comparison_comp
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [MonoidalClosed C]
    {D : Type uD} [Category.{vD} D] [MonoidalCategory D] [MonoidalClosed D]
    (F : C ⥤ D) [F.LaxMonoidal] (K M N : C) :
    μ F ((ihom K).obj M) ((ihom M).obj N) ≫
        F.map (MonoidalClosed.comp K M N) ≫ (ihomComparison F K).natTrans.app N =
      ((ihomComparison F K).natTrans.app M ⊗ₘ (ihomComparison F M).natTrans.app N) ≫
        MonoidalClosed.comp (F.obj K) (F.obj M) (F.obj N) := by
  rw [comp_eq, comparison_curry]
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, uncurry_natural_left, comp_eq, uncurry_curry]
  simp only [compTranspose_eq, F.map_comp]
  rw [associativity_inv_assoc]
  simp only [tensorHom_def, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [associator_inv_naturality_right_assoc, associator_inv_naturality_middle_assoc,
    whisker_exchange_assoc, ← comp_whiskerRight_assoc, ihomComparison_ev,
    ihomComparison_ev]
  simp only [comp_whiskerRight, Category.assoc]
  have hn := μ_natural_left_assoc F ((ihom.ev K).app M) ((ihom M).obj N)
    (F.map ((ihom.ev M).app N))
  dsimp only [Functor.id_obj, Functor.comp_obj] at hn
  rw [hn]
  rfl

/-- Evaluation transposes are uniquely characterized by evaluation, natural in both
variables, and compatible with transposition, internal composition, monoidal natural
identification of successive functors, and the identity functor.

Source: literature/blueprint/master/blueprint/sec-six-functors/
sk-prop-sf-biduality-general/thm-coef-finite-hom.md, proof final paragraph
(blueprint: lem-coef-evaluation-transpose-coherence).

Proof plan (the node's eleven steps):
1. Uncurrying sends `q` to evaluation after `q ⊗ 1`; naturality gives
   `U(H(a,b) q r) = b U(q) (r ⊗ a)`. It is injective by the adjunction bijection.
2. The comparison is the transpose of the image of evaluation after the tensorator;
   applying uncurrying proves the evaluation equation and its uniqueness.
3. For `a : T ⊗ K ⟶ M`, tensorator naturality and step 2 identify the uncurrying
   of `F(a♯)` followed by the comparison with the tensorator followed by `F(a)`.
4. Uncurry both covariant naturality expressions; evaluation naturality and
   tensorator naturality identify them, so injectivity proves equality.
5. Do the same for precomposition in `K`; bifunctoriality combines the two variances.
6. Internal composition is characterized by two successive evaluations. Keep the
   associator in that formula and use the strong monoidal associativity axiom.
7. Uncurry the image of source composition followed by the comparison, using step 2
   and tensorator naturality, obtaining the image of the two evaluations.
8. Uncurry the composite of the two comparisons followed by target composition.
   Associator naturality, step 2 twice, and step 6 give the same expression; cancel U.
9. For `F ⋙ G`, its tensorator is the tensorator of G followed by G of that of F.
   Uncurrying the two successive comparisons gives its evaluation transpose.
10. For `h : F ⋙ G ≅ J`, monoidality and evaluation naturality identify both sides
    after uncurrying and tensoring by `h.hom.app K`. Cancel that isomorphism and U.
11. For the identity functor its tensorator is the identity, so the comparison and
    the identity have the same uncurrying. No comparison is assumed invertible.

The displayed symmetries translate precisely the source's right-tensor convention;
associators in internal composition remain those of `MonoidalClosed.comp`.
-/
theorem evaluationTransposeCoherence
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C]
    {D : Type uD} [Category.{vD} D] [MonoidalCategory D] [SymmetricCategory D]
    [MonoidalClosed D]
    {E : Type uE} [Category.{vE} E] [MonoidalCategory E] [SymmetricCategory E]
    [MonoidalClosed E] (F : C ⥤ D) [F.Braided] :
    (∀ (K M : C) (q : F.obj ((ihom K).obj M) ⟶ (ihom (F.obj K)).obj (F.obj M)),
      (q ▷ F.obj K ≫
          (β_ ((ihom (F.obj K)).obj (F.obj M)) (F.obj K)).hom ≫
          (ihom.ev (F.obj K)).app (F.obj M) =
        μ F ((ihom K).obj M) K ≫
          F.map ((β_ ((ihom K).obj M) K).hom ≫ (ihom.ev K).app M)) ↔
      q = (ihomComparison F K).natTrans.app M) ∧
    (∀ {K K' M M' : C} (a : K' ⟶ K) (b : M ⟶ M'),
      F.map ((pre a).app M ≫ (ihom K').map b) ≫
          (ihomComparison F K').natTrans.app M' =
        (ihomComparison F K).natTrans.app M ≫
          (pre (F.map a)).app (F.obj M) ≫ (ihom (F.obj K')).map (F.map b)) ∧
    (∀ {T K M : C} (a : T ⊗ K ⟶ M),
      F.map (curry ((β_ K T).hom ≫ a)) ≫ (ihomComparison F K).natTrans.app M =
        curry ((β_ (F.obj K) (F.obj T)).hom ≫ μ F T K ≫ F.map a)) ∧
    (∀ (K M N : C),
      μ F ((ihom M).obj N) ((ihom K).obj M) ≫
          F.map ((β_ ((ihom M).obj N) ((ihom K).obj M)).hom ≫
            MonoidalClosed.comp K M N) ≫ (ihomComparison F K).natTrans.app N =
        ((ihomComparison F M).natTrans.app N ⊗ₘ (ihomComparison F K).natTrans.app M) ≫
          (β_ ((ihom (F.obj M)).obj (F.obj N))
            ((ihom (F.obj K)).obj (F.obj M))).hom ≫
          MonoidalClosed.comp (F.obj K) (F.obj M) (F.obj N)) ∧
    (∀ (G : D ⥤ E) (J : C ⥤ E) [G.Braided] [J.Braided]
        (h : F ⋙ G ≅ J) [NatTrans.IsMonoidal h.hom] (K M : C),
      h.hom.app ((ihom K).obj M) ≫ (ihomComparison J K).natTrans.app M =
        G.map ((ihomComparison F K).natTrans.app M) ≫
          (ihomComparison G (F.obj K)).natTrans.app (F.obj M) ≫
          (pre (h.inv.app K)).app (G.obj (F.obj M)) ≫
          (ihom (J.obj K)).map (h.hom.app M)) ∧
    (∀ (K M : C), (ihomComparison (𝟭 C) K).natTrans.app M = 𝟙 ((ihom K).obj M)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K M q
    rw [BraidedCategory.braiding_naturality_left_assoc, F.map_comp,
      Functor.LaxBraided.braided_assoc]
    rw [cancel_epi, ← uncurry_eq, ← ihomComparison_ev F K M, ← uncurry_eq]
    exact ⟨fun h ↦ uncurry_injective h, fun h ↦ congrArg uncurry h⟩
  · intro K K' M M' a b
    have hn := (ihomComparison F K').natTrans.naturality b
    dsimp only [Functor.comp_map] at hn
    rw [F.map_comp, Category.assoc, hn, map_pre_app_comp_ihomComparison_app_assoc]
  · intro T K M a
    rw [comparison_curry, F.map_comp, Functor.LaxBraided.braided_assoc]
  · intro K M N
    simp only [F.map_comp, Category.assoc]
    rw [Functor.LaxBraided.braided_assoc, comparison_comp,
      ← BraidedCategory.braiding_naturality_assoc]
    rfl
  · intro G J _ _ h _ K M
    have hn := ihomComparison_app_comp_map_app h.hom K M
    calc
      _ = ((ihomComparison (F ⋙ G) K).natTrans.app M ≫
          (ihom ((F ⋙ G).obj K)).map (h.hom.app M)) ≫
          (pre (h.inv.app K)).app (J.obj M) := by
        rw [hn, Category.assoc, Category.assoc, ← NatTrans.comp_app, ← pre_map]
        simp
      _ = (ihomComparison (F ⋙ G) K).natTrans.app M ≫
          (pre (h.inv.app K)).app (G.obj (F.obj M)) ≫
          (ihom (J.obj K)).map (h.hom.app M) := by
        rw [Category.assoc, (pre (h.inv.app K)).naturality]
        rfl
      _ = _ := by rw [ihomComparison_comp_app]; simp only [Category.assoc]
  · intro K M
    rw [ihomComparison_app_eq_curry]
    simp only [Functor.LaxMonoidal.id_μ, Category.id_comp, Functor.id_map]
    simpa only [uncurry_id_eq_ev] using (curry_uncurry (𝟙 ((ihom K).obj M)))

end CategoryTheory.Functor.Braided
