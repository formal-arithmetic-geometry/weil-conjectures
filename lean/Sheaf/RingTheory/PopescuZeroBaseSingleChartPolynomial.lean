/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.RingTheory.PopescuLiftPresentation

/-! # Eliminating auxiliary variables in a single chart

Source: Stacks Project, Tag 07CP, displayed calculation of (D_k / pi D_k) localized at a_k.
(blueprint: lem-weil-pbc-popescu-zero-base-single-chart-polynomial).
-/

@[expose] public section

universe a c b

open scoped TensorProduct

namespace Algebra.PopescuLiftPresentation

/-- The single-chart quotient becomes a polynomial algebra when pi is killed.

Source: Stacks Project, Tag 07CP, the displayed three-line calculation for D_k modulo pi.
(blueprint: lem-weil-pbc-popescu-zero-base-single-chart-polynomial).

Proof: Tensor the quotient by all u_l=f_l-pi*z_l and the single chart's
p_kl with B, then invert the image of a_k. Since pi is zero in B, the u_l
become all f_l=0. Reducing coefficients modulo pi squared changes nothing.
Thus the coefficient quotient is the scalar extension of reducedQuotient.
Localization commutes with scalar extension, identifying the coefficient ring
with B tensor over R/(pi squared) with reducedQuotient[1/reducedElement(k)].
The chart relations become a_k*z_l=sum h_klj*z_j. Normalization makes those
indexed by E_k zero. Since a_k is a unit, solve the remaining equations uniquely
for z_l outside E_k. Send each free variable to z_j and send each other z_l
back to a_k inverse times sum h_klj*z_j. These maps are inverse on the coefficient
ring and on every variable. Quotient and tensor-product universal properties
construct the maps, and ULift is removed by its algebra equivalence. This is a
calculation for a quotient with only one chart's equations: no other chart's
relations, conormal basis, smoothness or differential basis is used. -/
theorem zero_base_single_chart_polynomial (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π)
    (hnorm : ∀ (k : Fin d.r) (l : Fin d.m), l ∈ d.E k →
      ∀ j : Fin d.m, d.h k l j = if l = j then d.a k else 0)
    (B : Type b) [CommRing B] [Algebra R B]
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) B]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) B]
    (hπ : algebraMap R B π = 0) (k : Fin d.r) :
    let J : Ideal d.polynomial := Ideal.span (Set.range (fun i : Fin d.m ⊕ Fin d.m ↦
      match i with
      | .inl j => d.equation (.inl j)
      | .inr l => d.equation (.inr (k, l))))
    Nonempty (MvPolynomial (d.E k)
      (B ⊗[R ⧸ Ideal.span ({π ^ 2} : Set R)]
        Localization.Away (d.reducedElement k)) ≃ₐ[B]
      Localization.Away (Algebra.TensorProduct.includeRight (R := R) (A := B)
        (ULift.up (Ideal.Quotient.mk J (d.includeX (d.a k)))))) := by
  sorry

end Algebra.PopescuLiftPresentation
