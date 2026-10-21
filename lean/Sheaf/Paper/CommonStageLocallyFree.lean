/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.DerivedPullbackTensorHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Local finite freeness in the rational common-stage category

Source: Bhatt--Scholze, Definition 6.8.3, Proposition 6.8.14(2), Remark 6.8.15;
blueprint dual representation sentence (blueprint: def-real-common-stage-lisse).
The local integral free models are chosen separately on each pro-etale chart.
There is no assertion that a global integral lisse lattice exists.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Pro-etale locally a finite sum of the rational coefficient unit, at finite stages.
The integer r may be zero and may vary with the chart. The ambient constructible object
and each local integral model use the recorded raw rationalization and stage inclusion.
Source: Bhatt--Scholze 6.8.3, 6.8.14(2), 6.8.15
(blueprint: def-real-common-stage-lisse). -/
def IsCommonStageLisse (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X : Scheme.{u}) [hX : ∀ x : X, Invertible (l : X.residueField x)]
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) : Prop :=
  ∃ (I : Type (u + 1)) (V : I → X.ProEt)
    (a : ∀ i : I, V i ⟶ ⊤_ X.ProEt),
    Sieve.ofArrows V a ∈ ProEt.topology X (⊤_ X.ProEt) ∧
      ∀ i : I, ∃ hV : ∀ x : (V i).left, Invertible (l : (V i).left.residueField x),
        ∃ (E : AlgebraicallyClosedCoefficients.Index l Ω) (r : ℕ)
          (M : sfIntegralConstructibleCategory l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) (V i).left),
          Nonempty (M.obj ≅ (DerivedCategory.singleFunctor _ 0).obj
            (SheafOfModules.free
              (R := completedIntegralCoefficientSheafUnrestricted l
                (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) (V i).left)
              (ULift.{u + 1} (Fin r)))) ∧
          Nonempty (((@commonStageDerivedPullback l _ Ω _ _ _ _ _
            (V i).hom hV hX).obj K) ≅
              (GeneralAlgebraicallyClosedCoefficients.inclusion E).obj
                ((sfRationalConstructibleLocalization l
                  (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) (V i).left).obj M))

end WeilConjectures
