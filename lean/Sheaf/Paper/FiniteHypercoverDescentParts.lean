module
public import Sheaf.Paper.FiniteSplitEtaleHypercover
import Sheaf.Paper.EtaleFiniteDataDescent
@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- Finite hypercover objects descend; this is the object and covering part of the
finite-data descent argument. Source: blueprint
lemma-weil-pbc-finite-hypercover-descent,
Detailed form proof, first two paragraphs.
(blueprint: lemma-weil-pbc-finite-hypercover-descent-objects) -/
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
  sorry
/-- Morphisms of finite hypercover truncations descend. Source: blueprint
lemma-weil-pbc-finite-hypercover-descent, Detailed form proof, final paragraph.
(blueprint: lemma-weil-pbc-finite-hypercover-descent-morphisms) -/
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
  sorry
/-- Equalities of finite hypercover morphisms descend. Source: blueprint
lemma-weil-pbc-finite-hypercover-descent, Detailed form proof, final paragraph.
(blueprint: lemma-weil-pbc-finite-hypercover-descent-equalities) -/
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
  sorry
end AlgebraicGeometry
