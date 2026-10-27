/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.TraceFormula.GradedLineFractionChart

/-! # Local comparison for graded line fraction tests

Source: Stacks Project, Constructions, Tags 01NK and 01O9
(blueprint: lem-trf-graded-line-fraction-test-local).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The comparison of a prescribed fraction morphism with the trivialized Proj map
holds on an open neighbourhood of every point of the test scheme.

This is the local geometric step in the proof of
`gradedLineFraction_test`.  The unit ideal hypothesis supplies a positive-degree
basic-open neighbourhood; the free-frame and fraction formulas identify the two
maps there.  The global equality is obtained from this local statement by
`Scheme.hom_ext_of_forall`.

Source: Stacks Project, Constructions, Tag 01NK, lemma-invertible-map-into-proj,
and Tag 01O9, lemma-invertible-map-into-relative-proj, characterizations (2) and
(3) (blueprint: lem-trf-graded-line-fraction-test-local).
-/
theorem gradedLineFraction_test_local
    {S T : Scheme.{u}} {h : T ⟶ S} {A : S.GradedAlgebraData} {L : T.Modules}
    (ψ : RelativeGradedLineMap h A L)
    (P : ∀ {W : T.Opens}, Γ(L, W) → (n : ℕ) → Γ(L.tensorPow n, W))
    (hP0 : ∀ (W : T.Opens) (l : Γ(L, W)), P l 0 = unitSectionsEquiv W 1)
    (hPs : ∀ (W : T.Opens) (l : Γ(L, W)) (n : ℕ),
      P l (n + 1) = tmulSection l (P l n))
    (c : GradedLineFractionCoefficients h A L)
    (hc : ∀ (U : S.affineOpens) (W : T.affineOpens) (hWU : W.1 ≤ h ⁻¹ᵁ U.1)
      (l : Γ(L, W.1)), IsFreeGenerator l → ∀ (n : ℕ) (a : A.grading U n),
      c U W hWU l n a • P l n =
        (L.tensorPow n).val.map (homOfLE hWU).op (ψ.component U n a))
    (ρ : ∀ i : GradedLineFractionChart h A L,
      HomogeneousLocalization.Away (A.grading i.U) i.e.val →+*
        Localization.Away (i.coefficient c))
    (hρ : GradedLineFractionChart.FractionFormula c ρ)
    (F : T ⟶ A.relProj)
    (hF : ∀ i : GradedLineFractionChart h A L, i.source c ≫ F = i.target c ρ)
    (W : Scheme.{u}) (j : W ⟶ T) (hj : IsOpenImmersion j)
    (V : S.affineOpens) (q : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (e : (tensorPullback j).obj L ≅ SheafOfModules.unit W.ringCatSheaf)
    (α : A.obj V →+* Γ(W, ⊤))
    (hα : ∀ (n : ℕ) (a : A.grading V n), α a =
      (unitSectionsEquiv ⊤).symm
        ((AlgebraicSpace.trivializedPower e n).hom.app ⊤ (ψ.evaluate j V q n a)))
    (hαgen : Ideal.map α (HomogeneousIdeal.irrelevant (A.grading V)).toIdeal = ⊤) :
    ∀ x : W, ∃ U : W.Opens, x ∈ U ∧
      U.ι ≫ j ≫ F =
        U.ι ≫ (Proj.fromOfGlobalSections (A.grading V) α hαgen ≫ A.relProjι V) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
