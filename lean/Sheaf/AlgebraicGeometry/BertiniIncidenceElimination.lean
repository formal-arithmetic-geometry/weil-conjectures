/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Elimination in a trivialized Bertini incidence chart

Source: Stacks Project, More on Morphisms, Tag 0G4F, final proof paragraph.
-/

@[expose] public section

universe u

open MvPolynomial

namespace Algebra

/-- Solving a linear incidence equation whose first coefficient is one gives a polynomial
ring in the remaining variables, with its specified substitution map.

Source: Stacks Project, More on Morphisms, Tag 0G4F, elimination of the first parameter.
(blueprint: lem-zl-bertini-incidence-elimination).

Proof: Separate the first variable using the multivariate/univariate polynomial equivalence.
The equation becomes X plus the constant polynomial sum g_i x_i. Evaluation at minus that
sum identifies the quotient with the coefficient polynomial ring. The substitution formula
holds on constants and on every variable, hence on all polynomials. -/
theorem exists_bertiniIncidenceElimination
    (A : Type u) [CommRing A] (n : ℕ) (g : Fin n → A) :
    ∃ e :
      (MvPolynomial (Fin (n + 1)) A ⧸ Ideal.span
        {(X 0 + ∑ i : Fin n, C (g i) * X i.succ :
          MvPolynomial (Fin (n + 1)) A)}) ≃ₐ[A] MvPolynomial (Fin n) A,
      ∀ p : MvPolynomial (Fin (n + 1)) A,
        e (Ideal.Quotient.mk _ p) =
          aeval (Fin.cases (-∑ i : Fin n, C (g i) * X i) X) p := by
  classical
  let t : MvPolynomial (Fin n) A := ∑ i : Fin n, C (g i) * X i
  let I : Ideal (MvPolynomial (Fin (n + 1)) A) :=
    Ideal.span {X 0 + ∑ i : Fin n, C (g i) * X i.succ}
  let J : Ideal (Polynomial (MvPolynomial (Fin n) A)) :=
    Ideal.span {Polynomial.X - Polynomial.C (-t)}
  have hJ : J = I.map (finSuccEquiv A n).toRingHom := by
    dsimp only [I]
    rw [Ideal.map_span, Set.image_singleton]
    dsimp only [J]
    apply congrArg Ideal.span
    apply congrArg Set.singleton
    simp [t, finSuccEquiv_apply]
  let e := (Ideal.quotientEquivAlg I J (finSuccEquiv A n) hJ).trans
    ((Polynomial.quotientSpanXSubCAlgEquiv (-t)).restrictScalars A)
  refine ⟨e, ?_⟩
  have h : e.toAlgHom.comp (Ideal.Quotient.mkₐ A I) =
      aeval (Fin.cases (-t) X) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;>
      change (Polynomial.quotientSpanXSubCAlgEquiv (-t))
        (Ideal.Quotient.mk _ ((finSuccEquiv A n) (X _))) = _ <;>
      simp [finSuccEquiv_X_zero, finSuccEquiv_X_succ]
  intro p
  exact DFunLike.congr_fun h p

end Algebra
