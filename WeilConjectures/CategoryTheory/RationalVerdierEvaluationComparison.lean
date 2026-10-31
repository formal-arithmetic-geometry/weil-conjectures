/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.EvaluationBidualComparisonTransport

/-! # Coherence of the canonical scalar dual comparison

Source: current blueprint thm-coef-rational-verdier, proof paragraphs 1 and 3.
(blueprint: lem-coef-rational-verdier-evaluation-comparison).

These equations do not require scalar extension to be an equivalence. They apply
whenever the internal-Hom mate is invertible at the specified objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v u' v' u'' v''
open CategoryTheory MonoidalCategory MonoidalClosed Opposite

namespace WeilConjectures.RationalVerdierCondensed

variable {C : Type u} {C' : Type u'} [Category.{v} C] [Category.{v'} C']
  [MonoidalCategory C] [MonoidalCategory C'] [MonoidalClosed C] [MonoidalClosed C']

/-- The canonical dual comparison intertwines the actual left evaluation maps.
Source: current blueprint rational duality, proof paragraph 1.
(blueprint: lem-coef-rational-verdier-evaluation-comparison).
Proof: expand the composite comparison and use naturality of uncurrying followed
by the defining evaluation equation for the lax-monoidal internal-Hom mate. -/
theorem evaluation (F : C ⥤ C') [F.LaxMonoidal]
    {W : C} {W' : C'} (w : F.obj W ≅ W') (K : C)
    (hβ : IsIso ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app W)) :
    F.obj K ◁ (evaluationDualComparison F w K hβ).hom ≫ (ihom.ev (F.obj K)).app W' =
      Functor.LaxMonoidal.μ F K _ ≫ F.map ((ihom.ev K).app W) ≫ w.hom := by
  dsimp only [evaluationDualComparison, Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
  rw [← uncurry_eq, uncurry_natural_right, uncurry_eq,
    Functor.LaxMonoidal.ihomComparison_ev, Category.assoc]

/-- Naturality in every ambient morphism, with contravariant precomposition.
Source: current blueprint rational duality, proof paragraphs 1 and 3.
(blueprint: lem-coef-rational-verdier-evaluation-comparison).
Proof: expand the comparison; move precomposition past the lax-monoidal mate
and then past the internal-Hom map of the dualizing-object identification. -/
theorem naturality (F : C ⥤ C') [F.LaxMonoidal]
    {W : C} {W' : C'} (w : F.obj W ≅ W') {K L : C} (f : L ⟶ K)
    (hK : IsIso ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app W))
    (hL : IsIso ((Functor.LaxMonoidal.ihomComparison F L).natTrans.app W)) :
    F.map ((pre f).app W) ≫ (evaluationDualComparison F w L hL).hom =
      (evaluationDualComparison F w K hK).hom ≫ (pre (F.map f)).app W' := by
  dsimp only [evaluationDualComparison, Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
  rw [← Category.assoc, Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app,
    Category.assoc, pre_comm_ihom_map, Category.assoc]

/-- Compatibility with the evaluation-defined double-dual arrow.
Source: current blueprint rational duality, proof paragraphs 1 and 3.
(blueprint: lem-coef-rational-verdier-evaluation-comparison).
Proof: uncurry the two candidate maps. The evaluation equation, tensorator
naturality and braidedness identify their untransposes. Cancel precomposition
with the dual comparison by its inverse. -/
theorem biduality [SymmetricCategory C] [SymmetricCategory C']
    (F : C ⥤ C') [F.Braided] {W : C} {W' : C'} (w : F.obj W ≅ W') (K : C)
    (hK : IsIso ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app W))
    (hDK : IsIso ((Functor.LaxMonoidal.ihomComparison F ((ihom K).obj W)).natTrans.app W)) :
    toIhomIhom W' (F.obj K) = F.map (toIhomIhom W K) ≫
      (evaluationDualComparison F w ((ihom K).obj W) hDK).hom ≫
      (pre (evaluationDualComparison F w K hK).inv).app W' := by
  have h : F.map (toIhomIhom W K) ≫
      (evaluationDualComparison F w ((ihom K).obj W) hDK).hom =
      toIhomIhom W' (F.obj K) ≫
        (pre (evaluationDualComparison F w K hK).hom).app W' := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_eq, evaluation,
      uncurry_pre_app, uncurry_toIhomIhom,
      BraidedCategory.braiding_naturality_left_assoc, evaluation,
      Functor.LaxMonoidal.μ_natural_right_assoc, ← F.map_comp_assoc,
      ← uncurry_eq, uncurry_toIhomIhom, F.map_comp,
      ← Functor.LaxBraided.braided_assoc]
    simp only [Category.assoc]
  rw [← Category.assoc, h, Category.assoc, ← NatTrans.comp_app, ← pre_map,
    Iso.inv_hom_id, pre_id, NatTrans.id_app, Category.comp_id]

/-- The normalized dual comparison respects composition of scalar functors.
Source: current blueprint rational duality, proof paragraph 3, associator equation.
(blueprint: lem-coef-rational-verdier-evaluation-comparison).
Proof: expand both comparisons, apply the composite internal-Hom mate equation,
and move the intermediate dualizing identification across the second mate by
naturality. Functoriality and associativity identify the remaining composites. -/
theorem composition {C'' : Type u''} [Category.{v''} C'']
    [MonoidalCategory C''] [MonoidalClosed C'']
    (F : C ⥤ C') (G : C' ⥤ C'') [F.LaxMonoidal] [G.LaxMonoidal]
    {W : C} {W' : C'} {W'' : C''} (w : F.obj W ≅ W') (v : G.obj W' ≅ W'')
    (K : C)
    (hF : IsIso ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app W))
    (hG : IsIso ((Functor.LaxMonoidal.ihomComparison G (F.obj K)).natTrans.app W'))
    (hFG : IsIso ((Functor.LaxMonoidal.ihomComparison (F ⋙ G) K).natTrans.app W)) :
    (evaluationDualComparison (F ⋙ G) (G.mapIso w ≪≫ v) K hFG).hom =
      G.map (evaluationDualComparison F w K hF).hom ≫
        (evaluationDualComparison G v (F.obj K) hG).hom := by
  dsimp only [evaluationDualComparison, Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
  rw [Functor.LaxMonoidal.ihomComparison_comp_app]
  simp only [Functor.map_comp, Functor.comp_obj, Category.assoc]
  have h := (Functor.LaxMonoidal.ihomComparison G (F.obj K)).natTrans.naturality w.hom
  dsimp only [Functor.comp_obj, Functor.comp_map] at h
  simpa only [Category.assoc] using congrArg
    (fun f ↦ G.map ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app W) ≫
      f ≫ (ihom (G.obj (F.obj K))).map v.hom) h.symm

end WeilConjectures.RationalVerdierCondensed
