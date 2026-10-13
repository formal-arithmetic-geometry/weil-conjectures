/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.RingTheory.PopescuLiftPresentation

/-! # Scalar extension and localization of the single-chart presentation

Source: Stacks Project, Tag 07CP, first two lines of the calculation modulo pi.
(blueprint: lem-weil-pbc-popescu-zero-base-single-chart-presentation).
-/

@[expose] public section

universe a c b

open scoped TensorProduct

namespace Algebra.PopescuLiftPresentation

variable {R : Type a} {Cbar : Type c} [CommRing R] [CommRing Cbar] {π : R}
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) Cbar]

/-- The explicit coefficient map: reduce, quotient, localize, and extend scalars. -/
noncomputable def singleChartCoefficient (d : PopescuLiftPresentation R Cbar π)
    (B : Type b) [CommRing B]
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) B] (k : Fin d.r) :
    MvPolynomial (Fin d.n) R →+*
      B ⊗[R ⧸ Ideal.span ({π ^ 2} : Set R)] Localization.Away (d.reducedElement k) :=
  (Algebra.TensorProduct.includeRight (R := R ⧸ Ideal.span ({π ^ 2} : Set R))
    (A := B)).toRingHom.comp
      ((algebraMap d.reducedQuotient (Localization.Away (d.reducedElement k))).comp
        ((Ideal.Quotient.mk d.reducedIdeal).comp
          (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span ({π ^ 2} : Set R))))))

/-- The linear relations over the explicitly localized coefficient ring. -/
noncomputable def singleChartLinearIdeal (d : PopescuLiftPresentation R Cbar π)
    (B : Type b) [CommRing B]
    [Algebra (R ⧸ Ideal.span ({π ^ 2} : Set R)) B] (k : Fin d.r) :
    Ideal (MvPolynomial (Fin d.m)
      (B ⊗[R ⧸ Ideal.span ({π ^ 2} : Set R)] Localization.Away (d.reducedElement k))) :=
  Ideal.span (Set.range (fun l ↦
    MvPolynomial.C (d.singleChartCoefficient B k (d.a k)) * MvPolynomial.X l -
      ∑ j : d.E k, MvPolynomial.C (d.singleChartCoefficient B k (d.h k l j)) *
        MvPolynomial.X (j : Fin d.m)))

/-- Scalar extension killing pi and localization give the displayed linear presentation.

Source: Stacks Project, Tag 07CP, first two lines of the calculation modulo pi.
(blueprint: lem-weil-pbc-popescu-zero-base-single-chart-presentation).

Proof: Split the original and auxiliary polynomial variables using the polynomial
universal property. Tensoring with B replaces coefficients by their images in B.
Because pi maps to zero, the original equations become f_l and the selected chart's
equations become a_k z_l minus the sum of h_klj z_j. First quotient by all the f_l
in the coefficient ring; reducing coefficients modulo pi squared is invisible in B,
so this is B tensor over R/(pi squared) with reducedQuotient. Inverting the image
of a_k commutes with scalar extension, polynomial extension, and the remaining
quotient: each assertion follows by constructing maps in both directions from their
universal properties and checking them on the coefficient ring and variables.
The resulting coefficient ring is K below, and its coefficient map is exactly
singleChartCoefficient. The remaining equations are exactly the generators of I.
Remove ULift by its canonical algebra equivalence. The two presentation maps fix
coefficients and each auxiliary variable; quotient and localization uniqueness show
that their composites are identities. Normalization of h is not required: this
statement retains every linear relation, including the free-variable relations. -/
theorem zero_base_single_chart_presentation (R : Type a) (Cbar : Type c)
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
    Nonempty ((MvPolynomial (Fin d.m)
      (B ⊗[R ⧸ Ideal.span ({π ^ 2} : Set R)] Localization.Away (d.reducedElement k))
        ⧸ d.singleChartLinearIdeal B k) ≃ₐ[B]
      Localization.Away (Algebra.TensorProduct.includeRight (R := R) (A := B)
        (ULift.up (Ideal.Quotient.mk J (d.includeX (d.a k)))))) := by
  sorry

end Algebra.PopescuLiftPresentation
