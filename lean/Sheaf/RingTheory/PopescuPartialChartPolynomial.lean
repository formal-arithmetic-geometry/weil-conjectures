/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.RingTheory.PopescuLiftPresentation

/-! # Polynomial model of a partial Popescu chart after killing pi

Source: Stacks Project, Tag 07CP, the calculation of the partial chart modulo pi.
(blueprint: lem-weil-pbc-popescu-partial-chart-polynomial).
-/

@[expose] public section

set_option autoImplicit false

universe a c b

open scoped TensorProduct

namespace Algebra

/-- Killing pi and inverting a_k turns the partial chart into a polynomial algebra.

Source: Stacks Project, Tag 07CP (lemma-lifting), the calculation of D_k/pi D_k.
(blueprint: lem-weil-pbc-popescu-partial-chart-polynomial).

Proof: Scalar extension to B sets pi to zero. The selected u_j become f_j for
j in E_k; the other chart equations become a_k z_l minus the indicated linear sum.
After inverting a_k, the cleared relations a_k f_l = sum h_klj f_j + pi^2 g_kl
show that the ideal of all original f_l equals the ideal of the selected f_j.
This identifies the coefficient quotient with the scalar extension of the reduced
quotient localized at a_k. Each equation outside E_k solves uniquely for z_l as
a_k inverse times sum h_klj z_j, and leaves the z_j in E_k free. Define the forward
map by these substitutions and the inverse by the original variables and free z_j.
The relations vanish under both maps, and checking x_i and all z_l proves their
composites are identities. Renumber the free variables using the finite-set
bijection with Fin(card E_k), and the ambient variables using finSumFinEquiv.
This argument also covers E_k empty or all auxiliary variables, and the zero
coefficient algebra. It uses no flatness, dimension equality or full-chart relation.
-/
theorem popescu_partial_chart_polynomial (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (B : Type b) [CommRing B] [Algebra R B]
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) B]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) B]
    (hπ : algebraMap R B π = 0) (k : Fin d.r)
    (F : Fin d.m → MvPolynomial (Fin (d.n + d.m)) R)
    (hF : ∀ l, F l = MvPolynomial.rename finSumFinEquiv
      (if l ∈ d.E k then d.equation (.inl l) else d.equation (.inr (k, l)))) :
    let S := MvPolynomial (Fin (d.n + d.m)) R ⧸ Ideal.span (Set.range F)
    let s : S := Ideal.Quotient.mk _
      (MvPolynomial.rename finSumFinEquiv (d.includeX (d.a k)))
    Nonempty (MvPolynomial (Fin (d.E k).card)
      (B ⊗[R ⧸ Ideal.span ({π ^ 2} : Set R)]
        Localization.Away (d.reducedElement k)) ≃ₐ[B]
      Localization.Away (Algebra.TensorProduct.includeRight (R := R) (A := B) s)) := by sorry

end Algebra
