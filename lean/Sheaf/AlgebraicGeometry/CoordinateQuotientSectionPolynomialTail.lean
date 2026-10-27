/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NN
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveCoordinateRingEulerPolynomial
import Sheaf.AlgebraicGeometry.GradedProjQuotientTwistComparison
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import Sheaf.AlgebraicGeometry.FiniteGradedModuleSectionTail
import Sheaf.RingTheory.StandardGradedHilbertFunction

/-!
# Coordinate quotient sections and their eventual polynomial

Source: Stacks Project, Tags 0AG7, 01MT, 01N1 and 00K1
(blueprint: lem-sfb-coordinate-quotient-section-polynomial-tail).

Degree-zero cohomology is written as global sections. Scalar restriction uses the
actual structure morphism to Spec k, including when the quotient ring is zero.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory Opposite HomogeneousLocalization
open AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
variable {k : Type u} [Field k] {N : ℕ}

/-- The specified pulled-back twist L_m, with no saturation of the quotient ideal.
Source: Stacks, Tags 01MN, 01N1
(blueprint: lem-sfb-coordinate-quotient-section-polynomial-tail). -/
def coordinateQuotientSectionTwist
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k))
    (m : ℕ) : (Proj (coordinateQuotientPiece J)).Modules :=
  (tensorPullback (coordinateQuotientImmersion J)).obj
    (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k) m)

/-- Global sections of L_m as a k-module, by restriction along its structure map.
Source: Stacks, Tags 01MT, 0AG7
(blueprint: lem-sfb-coordinate-quotient-section-polynomial-tail). -/
def coordinateQuotientTwistSections
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k))
    (m : ℕ) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (coordinateQuotientImmersion J ≫
        Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (N + 1))) k).appTop).hom)).obj
    ((RingedSpace.globalSectionsFunctor (Proj (coordinateQuotientPiece J)).toRingedSpace).obj
      (coordinateQuotientSectionTwist J m))

/-- The pulled-back coordinate basis e_j on D_+(u_j).
Source: Stacks, Tag 01N1
(blueprint: lem-sfb-coordinate-quotient-section-polynomial-tail). -/
def coordinateQuotientSectionFrame
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k))
    (m : ℕ) (j : ULift.{u} (Fin (N + 1))) :
    Γ(coordinateQuotientSectionTwist J m,
      Proj.basicOpen (coordinateQuotientPiece J)
        (Ideal.Quotient.mk J.toIdeal (MvPolynomial.X j))) :=
  tensorPullbackSection (coordinateQuotientImmersion J)
    (Proj.twist (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k) m)
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k)
      (MvPolynomial.X j)) (Proj.twistPowSection m (MvPolynomial.isHomogeneous_X k j))

/-- The normalized twist comparison, the canonical linear section maps in every degree,
and their eventual bijectivity and polynomial dimensions, for the actual quotient.
Source: Stacks, coherent.tex Tag 0AG7; constructions.tex Tags 01MT, 01N1;
algebra.tex Tags 00K0, 00K1
(blueprint: lem-sfb-coordinate-quotient-section-polynomial-tail).
Proof: (1) If J is the unit ideal, the quotient and Proj are zero and empty; take bound
zero and polynomial zero. Otherwise J contains no nonzero constant, so A_0 = k.
The quotient grading gives degree-one generators u_j, whose charts cover Proj, and
A is a finite graded module over itself (def-sfb-coordinate-quotient-grading,
def-pc-proj, def-pc-standard-graded-algebra).
(2) Invert lem-sfb-graded-proj-quotient-twist-comparison to obtain theta. Its coordinate
normalization gives the displayed frames, and u_i^m = (u_i/u_j)^m u_j^m gives their
transition on overlaps, including empty charts (def-weil-pbc-proj-twisting-sheaf).
(3) The canonical section of h is h/1; in a coordinate frame it is (h/u_j^m)e_j.
Compose this section with theta. Gluing gives the displayed k-linear maps in every
degree. Apply lem-sfb-finite-graded-module-section-tail to A as a graded module over
itself, extended by zero in negative degrees, to obtain eventual bijectivity.
(4) Apply lem-trf-standard-graded-hilbert-function to the regular graded module A to
get finite-dimensional pieces and its eventual rational polynomial. Take the maximum
of the bounds. The bijective linear section map identifies the two dimensions.
No saturation, nonempty chart, or nonempty Proj is used. -/
theorem coordinateQuotient_section_polynomial_tail
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k)) :
    ∃ θ : ∀ m : ℕ, Proj.twist (coordinateQuotientPiece J) m ≅
        coordinateQuotientSectionTwist J m,
      (∀ (m : ℕ) (j : ULift.{u} (Fin (N + 1))),
        (θ m).hom.app (Proj.basicOpen (coordinateQuotientPiece J)
          (Ideal.Quotient.mk J.toIdeal (MvPolynomial.X j)))
          (Proj.twistPowSection m
            ((coordinateQuotientGradedMap J).map_mem (MvPolynomial.isHomogeneous_X k j))) =
          coordinateQuotientSectionFrame J m j) ∧
      (∀ (m : ℕ) (i j : ULift.{u} (Fin (N + 1)))
        (W : (Proj (coordinateQuotientPiece J)).Opens)
        (hi : W ≤ Proj.basicOpen (coordinateQuotientPiece J)
          (Ideal.Quotient.mk J.toIdeal (MvPolynomial.X i)))
        (hj : W ≤ Proj.basicOpen (coordinateQuotientPiece J)
          (Ideal.Quotient.mk J.toIdeal (MvPolynomial.X j))),
        (coordinateQuotientSectionTwist J m).presheaf.map (homOfLE hi).op
          (coordinateQuotientSectionFrame J m i) =
        (Proj (coordinateQuotientPiece J)).presheaf.map (homOfLE hj).op
          (Proj.awayToSection (coordinateQuotientPiece J)
            (Ideal.Quotient.mk J.toIdeal (MvPolynomial.X j))
            (Away.mk (coordinateQuotientPiece J)
              ((coordinateQuotientGradedMap J).map_mem (MvPolynomial.isHomogeneous_X k j))
              1 (Ideal.Quotient.mk J.toIdeal (MvPolynomial.X i))
              ((coordinateQuotientGradedMap J).map_mem
                (MvPolynomial.isHomogeneous_X k i)))) ^ m •
          (coordinateQuotientSectionTwist J m).presheaf.map (homOfLE hj).op
            (coordinateQuotientSectionFrame J m j)) ∧
      ∃ σ : ∀ m : ℕ, coordinateQuotientPiece J m →ₗ[k] coordinateQuotientTwistSections J m,
        (∀ (m : ℕ) (h : coordinateQuotientPiece J m)
          (j : ULift.{u} (Fin (N + 1))),
          (coordinateQuotientSectionTwist J m).presheaf.map
            (homOfLE (le_top : Proj.basicOpen (coordinateQuotientPiece J)
              (Ideal.Quotient.mk J.toIdeal (MvPolynomial.X j)) ≤ ⊤)).op (σ m h) =
          Proj.awayToSection (coordinateQuotientPiece J)
            (Ideal.Quotient.mk J.toIdeal (MvPolynomial.X j))
            (Away.mk (coordinateQuotientPiece J)
              ((coordinateQuotientGradedMap J).map_mem (MvPolynomial.isHomogeneous_X k j))
              m h (by simpa only [smul_eq_mul, mul_one] using h.property)) •
            coordinateQuotientSectionFrame J m j) ∧
        (∀ m : ℕ, Module.Finite k (coordinateQuotientPiece J m)) ∧
        ∃ (a : ℕ) (P : Polynomial ℚ), ∀ m : ℕ, a ≤ m →
          Function.Bijective (σ m) ∧
          P.eval (m : ℚ) = (Module.finrank k (coordinateQuotientPiece J m) : ℚ) ∧
          P.eval (m : ℚ) = (Module.finrank k (coordinateQuotientTwistSections J m) : ℚ) := by
  sorry

end
end AlgebraicGeometry
