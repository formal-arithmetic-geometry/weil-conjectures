/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.RingTheory.PopescuLiftPresentation

/-! # Redundancy of the full equations in the single zero-base chart

Source: Stacks Project, Tag 07CP, comparison of the conormal expressions on two charts.
(blueprint: lem-weil-pbc-popescu-zero-base-chart-relations).
-/

@[expose] public section

universe a c b

open scoped TensorProduct

namespace Algebra.PopescuLiftPresentation

/-- Every chart relation vanishes in the localized single-chart quotient over B.

Source: Stacks Project, Tag 07CP, final comparison calculation modulo pi.
(blueprint: lem-weil-pbc-popescu-zero-base-chart-relations).

Proof: In the single-chart quotient modulo pi all f_l vanish and the
k-th linear equations hold. For another chart k' put
b_j=a_k'*h_klj-sum h_k'lj'*h_kj'j. Compare the two cleared expressions for
a_k*a_k'*f_l in the reduced conormal module. Its specified basis on E_k implies
b_j=0 in reducedQuotient localized at a_k. Clear its localization denominator:
a power of a_k times b_j belongs to the reduced ideal. Lift this membership
to R[x]; the error is a multiple of pi squared. These terms vanish after tensoring
with B, since every f_l vanishes and pi maps to zero. Therefore b_j vanishes in
the localized single-chart quotient. Expand
 a_k*p_k'l-a_k'*p_kl+sum h_k'lj'*p_kj'.
Modulo pi this is sum b_j*z_j. All terms except a_k*p_k'l vanish, so invertibility
of a_k kills p_k'l as well. The original u_l already vanish by the quotient's
definition. This proves the assertion for every generator of the full defining
ideal without flatness, primes or equality of annihilators. The coefficient
calculation is performed before scalar extension, so it applies to arbitrary B,
including the zero ring and nonflat scalar extensions. -/
theorem zero_base_chart_relations (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] [Algebra R Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π) (hd : d.Prepared)
    (B : Type b) [CommRing B] [Algebra R B]
    (hπ : algebraMap R B π = 0) (k : Fin d.r)
    (k' : Fin d.r) (l : Fin d.m) :
    let J : Ideal d.polynomial := Ideal.span (Set.range (fun i : Fin d.m ⊕ Fin d.m ↦
      match i with
      | .inl j => d.equation (.inl j)
      | .inr l => d.equation (.inr (k, l))))
    let Dk := ULift.{c} (d.polynomial ⧸ J)
    let t := Algebra.TensorProduct.includeRight (R := R) (A := B)
      (ULift.up (Ideal.Quotient.mk J (d.includeX (d.a k))))
    algebraMap (B ⊗[R] Dk) (Localization.Away t)
      (Algebra.TensorProduct.includeRight (R := R) (A := B)
        (ULift.up (Ideal.Quotient.mk J (d.equation (.inr (k', l)))))) = 0 := by
  sorry

end Algebra.PopescuLiftPresentation
