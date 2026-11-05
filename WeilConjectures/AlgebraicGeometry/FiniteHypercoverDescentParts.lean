/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
import all WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentStages

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
  exact finite_hypercover_descent_of_diagram_models D c hc r U
    (split_diagram_model D c hc r U)

end AlgebraicGeometry
