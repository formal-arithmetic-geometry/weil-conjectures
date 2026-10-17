/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentObjects

/-!
# Blueprint statements

lemma-weil-pbc-finite-hypercover-descent-objects, lemma-weil-pbc-finite-hypercover-descent-
morphisms, lemma-weil-pbc-finite-hypercover-descent-equalities.
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Blueprint: lemma-weil-pbc-finite-hypercover-descent-objects. -/
theorem finite_hypercover_descent_objects
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    ∀ (r : ℕ) (U : TruncatedFiniteSplitEtaleHypercover c.pt r),
      ∃ (i : Iᵒᵖ) (Ui : TruncatedFiniteSplitEtaleHypercover (D.obj i) r),
        Ui.IsBaseChange (c.π.app i) U ∧
          ∀ (j : Iᵒᵖ) (h : j ⟶ i) (n : Fin (r + 1)),
            Surjective ((Over.pullback (D.map h)).map
              ((Scheme.Etale.forget (D.obj i)).map (Ui.matchingMap n))).left := by
  intro r U
  obtain ⟨i, Ui, hUi⟩ := exists_truncatedFiniteSplitEtaleHypercover_isBaseChange hc U
  exact ⟨i, Ui, hUi, fun j h n ↦ surjective_overPullback_map_left _ _ (Ui.matching_cover n)⟩

/-- Blueprint: lemma-weil-pbc-finite-hypercover-descent-morphisms. -/
theorem finite_hypercover_descent_morphisms
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    ∀ (r : ℕ) (i : Iᵒᵖ)
      (U V : TruncatedFiniteSplitEtaleHypercover (D.obj i) r)
      (φ : U.diagram ⋙ Over.pullback (c.π.app i) ⟶
        V.diagram ⋙ Over.pullback (c.π.app i)),
      ∃ (j : Iᵒᵖ) (h : j ⟶ i)
        (ψ : U.diagram ⋙ Over.pullback (D.map h) ⟶
          V.diagram ⋙ Over.pullback (D.map h)),
        ∀ Δ : (SimplexCategory.Truncated r)ᵒᵖ,
          (Over.pullback (c.π.app j)).map (ψ.app Δ) ≫
              (((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
                eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f)
                  (c.w h))).app (V.diagram.obj Δ)).hom =
            (((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
              eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f)
                (c.w h))).app (U.diagram.obj Δ)).hom ≫ φ.app Δ := by
  intro r i U V φ
  obtain ⟨j, h, ψ, hψ⟩ := exists_natTrans_descent D hc U.isQcqsEtale_diagram_obj
    V.isQcqsEtale_diagram_obj φ
  exact ⟨j, h, ψ, hψ⟩

/-- Blueprint: lemma-weil-pbc-finite-hypercover-descent-equalities. -/
theorem finite_hypercover_descent_equalities
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    ∀ (r : ℕ) (i : Iᵒᵖ)
      (U V : TruncatedFiniteSplitEtaleHypercover (D.obj i) r)
      (φ ψ : U.diagram ⟶ V.diagram),
      Functor.whiskerRight φ (Over.pullback (c.π.app i)) =
        Functor.whiskerRight ψ (Over.pullback (c.π.app i)) →
      ∃ (j : Iᵒᵖ) (h : j ⟶ i),
        Functor.whiskerRight φ (Over.pullback (D.map h)) =
          Functor.whiskerRight ψ (Over.pullback (D.map h)) := by
  intro r i U V φ ψ hφψ
  exact (stageEventually_whiskerRight_eq D hc U.isQcqsEtale_diagram_obj
    V.isQcqsEtale_diagram_obj φ ψ hφψ).exists_hom

end AlgebraicGeometry
