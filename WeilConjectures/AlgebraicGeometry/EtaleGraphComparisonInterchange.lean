/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphInterchangeData
import WeilConjectures.AlgebraicGeometry.EtaleGraphProductRowPasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkMiddlePasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkSidePasting

/-! # Graph comparisons and proper/open interchange

## References

* Stacks Project, Tag 0F7J
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

private theorem cancel_product_boundaries
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F₁ F₂ F₀ : C ⥤ D} {G₁ G₂ G₀ : D ⥤ E} {H₁ H₂ H₀ : C ⥤ E}
    (a₁ : F₁ ≅ F₀) (a₂ : F₂ ≅ F₀) (b₁ : G₁ ≅ G₀) (b₂ : G₂ ≅ G₀)
    (c₁ : H₁ ≅ H₀) (c₂ : H₂ ≅ H₀)
    (I₁ : F₁ ⋙ G₁ ≅ H₁) (I₂ : F₂ ⋙ G₂ ≅ H₂) (U : F₀ ⋙ G₀ ≅ H₀)
    (h₁ : I₁.hom ≫ c₁.hom =
      Functor.whiskerRight a₁.hom G₁ ≫ Functor.whiskerLeft F₀ b₁.hom ≫ U.hom)
    (h₂ : I₂.hom ≫ c₂.hom =
      Functor.whiskerRight a₂.hom G₂ ≫ Functor.whiskerLeft F₀ b₂.hom ≫ U.hom) :
    I₁.hom ≫ (c₁ ≪≫ c₂.symm).hom =
      Functor.whiskerRight (a₁ ≪≫ a₂.symm).hom G₁ ≫
        Functor.whiskerLeft F₂ (b₁ ≪≫ b₂.symm).hom ≫ I₂.hom := by
  apply (cancel_mono c₂.hom).1
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [h₁, h₂]
  ext M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  rw [← b₂.inv.naturality_assoc (a₂.hom.app M),
    ← b₁.hom.naturality_assoc (a₂.hom.app M)]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp, Category.comp_id, Iso.inv_hom_id_app_assoc]

private theorem shrink_cancel
    {C : Type*} [Category C] {B O₁ O₂ N₁ N₂ F₁ F₂ : C}
    (a₁ : B ≅ O₁) (a₂ : B ≅ O₂) (m₁ : O₁ ≅ N₁) (m₂ : O₂ ≅ N₂)
    (b₁ : F₁ ≅ N₁) (b₂ : F₂ ≅ N₂) (T : N₁ ≅ N₂) (I : F₁ ≅ F₂)
    (hs : b₁.hom ≫ T.hom = I.hom ≫ b₂.hom)
    (hm : m₁.hom ≫ T.hom = (a₁.symm ≪≫ a₂).hom ≫ m₂.hom) :
    ((a₁ ≪≫ m₁ ≪≫ b₁.symm).symm ≪≫ (a₂ ≪≫ m₂ ≪≫ b₂.symm)).hom = I.hom := by
  apply (cancel_epi (a₁ ≪≫ m₁ ≪≫ b₁.symm).hom).1
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  apply (cancel_mono b₂.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hs]
  simp only [Iso.inv_hom_id_assoc]
  rw [hm]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

private theorem graphComparison_shrink
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z W : Scheme.{u}} {h : X ⟶ Z} (c : Compactification h)
    (H : EtaleGraphPresentation h) (a' : X ⟶ W) (v : W ⟶ H.U)
    [IsProper a'] [IsOpenImmersion v] (fac : a' ≫ v = H.a) :
    (etaleGraphComparison A c H (H.shrink a' v fac)).hom =
      (etaleGraphShrinkInterchange A H a' v fac).hom := by
  let S := H.shrink a' v fac
  have hside := etaleGraphShrinkSidePasting A c H a' v fac
  have hmiddle := etaleGraphShrinkMiddlePasting A c H a' v fac
  have hfrom (t : EtaleGraphPresentation h) :
      etaleGraphComparisonFromOpen A c t =
        t.graphSide₁ c A ≪≫ t.graphMiddle c A ≪≫ (t.graphSide₂ c A).symm := by
    apply Iso.ext
    simp only [etaleGraphComparisonFromOpen, locallyClosedGraphIso,
      EtaleGraphPresentation.graphSide₁, EtaleGraphPresentation.graphSide₂,
      EtaleGraphPresentation.graphMiddle, Iso.trans_hom, Category.assoc]
  unfold etaleGraphComparison
  rw [hfrom H, hfrom S]
  exact shrink_cancel (H.graphSide₁ c A) (S.graphSide₁ c A)
    (H.graphMiddle c A) (S.graphMiddle c A) (H.graphSide₂ c A) (S.graphSide₂ c A)
    (H.graphNeighborhoodTriangle c A a' v fac) (etaleGraphShrinkInterchange A H a' v fac)
    hside hmiddle

/-- Product-graph comparisons identify the elementary neighborhood move and intertwine
proper/open interchange for arbitrary two supplied diagrams (Stacks, Tag 0F7J). -/
theorem etaleGraphComparisonInterchange (A : Type (u + 1)) [CommRing A] [Finite A] :
    (∀ {X Z W : Scheme.{u}} {h : X ⟶ Z} (c : Compactification h)
      (H : EtaleGraphPresentation h) (a' : X ⟶ W) (v : W ⟶ H.U)
      [IsProper a'] [IsOpenImmersion v] (fac : a' ≫ v = H.a),
      (etaleGraphComparison A c H (H.shrink a' v fac)).hom =
        (etaleGraphShrinkInterchange A H a' v fac).hom) ∧
    (∀ {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
      (cf : Compactification f) (ch : Compactification (f ≫ g))
      (d₁ d₂ : EtaleGraphInterchangeDiagram f g),
      (etaleGraphDiagramInterchange A d₁).hom ≫
          (etaleGraphComparison A ch d₁.compositePresentation d₂.compositePresentation).hom =
        Functor.whiskerRight
            (etaleGraphComparison A cf d₁.sourcePresentation d₂.sourcePresentation).hom
            ((EtaleGraphPresentation.ofCompactification d₁.compactification).functor A) ≫
          Functor.whiskerLeft (d₂.sourcePresentation.functor A)
            (etaleGraphComparison A d₁.compactification
              (EtaleGraphPresentation.ofCompactification d₁.compactification)
              (EtaleGraphPresentation.ofCompactification d₂.compactification)).hom ≫
          (etaleGraphDiagramInterchange A d₂).hom) := by
  constructor
  · intro X Z W h c H a' v ha hv fac
    exact graphComparison_shrink A c H a' v fac
  · intro X Y Z f g cf ch d₁ d₂
    have hf := etalePairwiseProductGraphNormalization A cf
      d₁.sourcePresentation d₂.sourcePresentation
    have hg := etalePairwiseProductGraphNormalization A d₁.compactification
      (EtaleGraphPresentation.ofCompactification d₁.compactification)
      (EtaleGraphPresentation.ofCompactification d₂.compactification)
    have hh := etalePairwiseProductGraphNormalization A ch
      d₁.compositePresentation d₂.compositePresentation
    rw [hf, hg, hh]
    exact cancel_product_boundaries
      (d₁.productSourceLambda d₂ A false) (d₁.productSourceLambda d₂ A true)
      (d₁.productMiddleLambda d₂ A false) (d₁.productMiddleLambda d₂ A true)
      (d₁.productCompositeLambda d₂ A false) (d₁.productCompositeLambda d₂ A true)
      (etaleGraphDiagramInterchange A d₁) (etaleGraphDiagramInterchange A d₂)
      (d₁.productInterchange d₂ A)
      (etaleGraphProductRowPasting A d₁ d₂ false)
      (etaleGraphProductRowPasting A d₁ d₂ true)

end AlgebraicGeometry.Etale
