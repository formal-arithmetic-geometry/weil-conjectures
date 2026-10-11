/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteSplitEtaleHypercover
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Finite étale hypercover skeleta descend

Source: literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-h2/
lemma-weil-pbc-finite-hypercover-descent.md (blueprint: lemma-weil-pbc-finite-hypercover-descent).
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- (blueprint: lemma-weil-pbc-finite-hypercover-descent)
Finite split étale truncations, their morphisms, and equality of morphisms descend.
The first clause chooses a stage after all matching arrows have become covers;
these covers persist at every later stage. The last two clauses use already
chosen stage models, as in Stacks 01ZM (2) and (3).
Source: blueprint lemma-weil-pbc-finite-hypercover-descent, Detailed form and proof;
Stacks Project, Limits, Lemma 01ZM.

Proof: use the finite-data descent argument on the finite family of nondegenerate
terms through degree `r`, all face, degeneracy, augmentation and splitting maps,
their simplicial identities, and the finitely many matching covering maps.  The
finite-limit base-change assertion identifies the descended matching schemes;
pass to a common later stage for all matching covers (Stacks 0EYL and 07RR).
For morphisms, descend the finitely many component maps and their naturality
identities using 01ZM (2) and (3). For equality, descend the finitely many
component equalities using 01ZM (3). These are precisely the three proof steps
of the node, using `lem-weil-pbc-etale-finite-data-descent` and
`lem-weil-pbc-etale-base-change-finite-limits`. No compatibility with chosen
splittings is imposed on morphisms, in accordance with the definition of refinement. -/
theorem finite_hypercover_descent
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    (∀ (r : ℕ) (U : TruncatedFiniteSplitEtaleHypercover c.pt r),
      ∃ (i : Iᵒᵖ) (Ui : TruncatedFiniteSplitEtaleHypercover (D.obj i) r),
        Ui.IsBaseChange (c.π.app i) U ∧
          ∀ (j : Iᵒᵖ) (h : j ⟶ i) (n : Fin (r + 1)),
            Surjective ((Over.pullback (D.map h)).map
              ((Scheme.Etale.forget (D.obj i)).map (Ui.matchingMap n))).left) ∧
    (∀ (r : ℕ) (i : Iᵒᵖ)
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
                (c.w h))).app (U.diagram.obj Δ)).hom ≫ φ.app Δ) ∧
    (∀ (r : ℕ) (i : Iᵒᵖ)
      (U V : TruncatedFiniteSplitEtaleHypercover (D.obj i) r)
      (φ ψ : U.diagram ⟶ V.diagram),
      Functor.whiskerRight φ (Over.pullback (c.π.app i)) =
        Functor.whiskerRight ψ (Over.pullback (c.π.app i)) →
      ∃ (j : Iᵒᵖ) (h : j ⟶ i),
        Functor.whiskerRight φ (Over.pullback (D.map h)) =
          Functor.whiskerRight ψ (Over.pullback (D.map h))) := by
  sorry

end AlgebraicGeometry
