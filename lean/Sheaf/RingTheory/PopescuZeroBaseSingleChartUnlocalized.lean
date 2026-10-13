/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.RingTheory.PopescuLiftPresentation

/-! # The unlocalized zero-base single-chart presentation

Source: Stacks Project, Tag 07CP, the coefficient reduction in the calculation modulo pi.
(blueprint: lem-weil-pbc-popescu-zero-base-single-chart-unlocalized).
-/

@[expose] public section

universe a c b

open scoped TensorProduct

namespace Algebra.PopescuLiftPresentation

/-- Before localization, scalar extension removes precisely the pi terms.

Source: Stacks Project, Tag 07CP (lemma-lifting), the first line of the calculation
modulo pi, before inverting the chart element.
(blueprint: lem-weil-pbc-popescu-zero-base-single-chart-unlocalized).

Proof: Tensor the original polynomial quotient with B. The tensor-quotient equivalence
identifies this with the quotient of B[x,z] by the coefficient images of the original
equations; the canonical ULift equivalence removes ULift. Since pi maps to zero,
the equations become f_l(x) and a_k(x)z_l minus the sum h_klj(x)z_j. Split the x and
z variables, and first quotient the coefficient polynomial ring B[x] by all f_l.
This yields the polynomial ring in z over B[x]/(f_l), modulo the displayed linear
relations. The map R to B factors through R/(pi squared), so the tensor-quotient and
polynomial base-change equivalences identify B[x]/(f_l) with
B tensor over R/(pi squared) with reducedQuotient. These maps send every polynomial
p(x) to its reduced coefficient class and each auxiliary variable to its own class.
The reverse maps are polynomial evaluation followed by the tensor and quotient
universal properties. Check the two composites on B, each x, and each z; polynomial,
tensor, and quotient extensionality gives identities and the stated coefficient
compatibility. This argument neither inverts a_k nor eliminates any variable and
requires no normalization or smoothness hypotheses. -/
theorem zero_base_single_chart_unlocalized (R : Type a) (Cbar : Type c)
    [CommRing R] [CommRing Cbar] (π : R)
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]
    (d : PopescuLiftPresentation R Cbar π)
    (B : Type b) [CommRing B] [Algebra R B]
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) B]
    [IsScalarTower R (R ⧸ Ideal.span ({π ^ 2} : Set R)) B]
    (hπ : algebraMap R B π = 0) (k : Fin d.r) :
    let J : Ideal d.polynomial := Ideal.span (Set.range (fun i : Fin d.m ⊕ Fin d.m ↦
      match i with
      | .inl j => d.equation (.inl j)
      | .inr l => d.equation (.inr (k, l))))
    let L := B ⊗[R ⧸ Ideal.span ({π ^ 2} : Set R)] d.reducedQuotient
    let β : MvPolynomial (Fin d.n) R →+* L :=
      (Algebra.TensorProduct.includeRight (R := R ⧸ Ideal.span ({π ^ 2} : Set R))
        (A := B)).toRingHom.comp ((Ideal.Quotient.mk d.reducedIdeal).comp
          (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span ({π ^ 2} : Set R)))))
    let I : Ideal (MvPolynomial (Fin d.m) L) := Ideal.span (Set.range (fun l ↦
      MvPolynomial.C (β (d.a k)) * MvPolynomial.X l -
        ∑ j : d.E k, MvPolynomial.C (β (d.h k l j)) * MvPolynomial.X (j : Fin d.m)))
    ∃ e : (MvPolynomial (Fin d.m) L ⧸ I) ≃ₐ[B]
        B ⊗[R] ULift (d.polynomial ⧸ J),
      ∀ p : MvPolynomial (Fin d.n) R,
        e (Ideal.Quotient.mk I (MvPolynomial.C (β p))) =
          Algebra.TensorProduct.includeRight (R := R) (A := B)
            (ULift.up (Ideal.Quotient.mk J (d.includeX p))) := by sorry

end Algebra.PopescuLiftPresentation
