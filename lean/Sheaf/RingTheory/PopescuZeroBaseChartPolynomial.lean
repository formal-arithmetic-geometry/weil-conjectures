/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.RingTheory.PopescuLiftPresentation

/-! # Polynomial model of a prepared lifting chart

Source: Stacks Project, Tag 07CP, polynomial chart calculation and comparison of charts.
(blueprint: lem-weil-pbc-popescu-zero-base-chart-polynomial).
-/

@[expose] public section

universe a c b

open scoped TensorProduct

namespace Algebra

/-- After a scalar extension killing pi, the prepared chart is a polynomial algebra
on E_k over the scalar extension of the smooth reduced coefficient chart.
Source: Stacks Project, Tag 07CP, polynomial chart calculation modulo pi and its
residue-field base change.
(blueprint: lem-weil-pbc-popescu-zero-base-chart-polynomial).

Proof: Since pi maps to zero in B, tensoring the explicit presentation of D with B
sets every f_l to zero and removes each pi g_kl term. Localizing at the image of s
inverts the same a_k: hc identifies their images modulo pi, and scalar extension
kills the difference, which belongs to pi D. Eliminate z_l outside E_k using the
k-th relations. Comparing the two conormal expressions for a_k a_k' f_l makes the
remaining coefficient b_j zero in the reduced coefficient chart, by its specified
basis. Clear a power of a_k before scalar extension, so this coefficient remains
zero after tensoring with B. All other chart relations are redundant. The coefficient
quotient is B tensor over R/pi squared with the reduced quotient localized at a_k;
localization commutes with scalar extension. Send the free z_j to themselves and
eliminated z_l to a_k inverse times their coefficient sum. These substitutions are
inverse on x_i and every z_l. ULift is removed by its algebra equivalence. This proves
the displayed B-algebra isomorphism without selecting a lifting algebra by existence. -/
theorem popescu_zero_base_chart_polynomial (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (c : Cbar →ₐ[R] (d.liftingAlgebra ⧸
      Ideal.span ({algebraMap R d.liftingAlgebra π} : Set d.liftingAlgebra)))
    (hc : ∀ i : Fin d.n, c (d.ε (MvPolynomial.X i)) = Ideal.Quotient.mk _ (d.x i))
    (B : Type b) [CommRing B] [Algebra R B]
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) B]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) B]
    (hπ : algebraMap R B π = 0) (k : Fin d.r) (s : d.liftingAlgebra)
    (hs : Ideal.Quotient.mk _ s = c (d.ε (d.reduced (d.a k)))) :
    Nonempty (MvPolynomial (d.E k)
      (B ⊗[R ⧸ Ideal.span ({π ^ 2} : Set R)]
        Localization.Away (d.reducedElement k)) ≃ₐ[B]
      Localization.Away
        (Algebra.TensorProduct.includeRight (R := R) (A := B) s)) := by sorry

end Algebra
