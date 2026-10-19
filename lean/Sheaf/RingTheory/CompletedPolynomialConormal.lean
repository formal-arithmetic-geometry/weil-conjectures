/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Continuous partial derivatives and the completed conormal differential

Source: Stacks Project, restricted.tex, Tags 0AKG and 0AJU
  (blueprint: def-per-completed-polynomial-conormal).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- The completed polynomial ring used in the presentation `P = A[x₁, …, xᵣ]̂`.
Source: Stacks Project, restricted.tex, Tags 0AJU and 0AKG
(blueprint: def-per-completed-polynomial-conormal). -/
@[reducible] def rigPolynomialCompletion {A : Type u} [CommRing A] (I : Ideal A) (r : ℕ) : Type u :=
  AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
    (MvPolynomial (Fin r) A)

/-- The partial derivative has a unique filtration-preserving extension to the completion.
Source: Stacks Project, restricted.tex, equation (NL) preceding Tag 0AJU
(blueprint: def-per-completed-polynomial-conormal).
Proof: the polynomial partial derivative is A-linear, so it preserves every I-power times
polynomials. It therefore induces compatible maps on the quotient tower; take their inverse
limit. Since A is Noetherian, IQ is finitely generated: the kernel of evaluation modulo
(IQ)^n is precisely (IP)^n. Thus the inverse-limit map preserves this filtration. Polynomials
approximate every element modulo (IP)^n; two such extensions therefore agree modulo every
power, and separatedness gives equality. -/
theorem existsUnique_rigPartialDerivative {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A)
    (r : ℕ) (i : Fin r) :
    ∃! d : rigPolynomialCompletion I r →ₗ[A] rigPolynomialCompletion I r,
      (∀ p : MvPolynomial (Fin r) A,
        d (algebraMap (MvPolynomial (Fin r) A) (rigPolynomialCompletion I r) p) =
          algebraMap (MvPolynomial (Fin r) A) (rigPolynomialCompletion I r)
            (MvPolynomial.pderiv i p)) ∧
      (∀ (n : ℕ) (x : rigPolynomialCompletion I r),
        x ∈ (I.map (algebraMap A (rigPolynomialCompletion I r))) ^ n →
          d x ∈ (I.map (algebraMap A (rigPolynomialCompletion I r))) ^ n) := by
  sorry

/-- The unique continuous extension of the polynomial partial derivative.
Source: Stacks Project, restricted.tex, equation (NL), Tag 0AJU
(blueprint: def-per-completed-polynomial-conormal).
The defining theorem specifies a unique map, rather than an arbitrary choice of data. -/
noncomputable def rigPartialDerivative {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A)
    (r : ℕ) (i : Fin r) :
    rigPolynomialCompletion I r →ₗ[A] rigPolynomialCompletion I r :=
  (existsUnique_rigPartialDerivative I r i).exists.choose

/-- The continuous partial derivative on the completed polynomial presentation, followed by
reduction modulo `J`, on the `i`-th coordinate.
Source: Stacks Project, restricted.tex, Tags 0AJU and 0AKG
(blueprint: def-per-completed-polynomial-conormal). -/
noncomputable def rigJacobianRawDifferential {A : Type u} [CommRing A]
    [IsNoetherianRing A] (r : ℕ) (I : Ideal A)
    (J : Ideal (rigPolynomialCompletion I r)) (i : Fin r) :
    J →ₗ[A] (rigPolynomialCompletion I r ⧸ J) :=
  ((Ideal.Quotient.mkₐ A J).toLinearMap.comp (rigPartialDerivative I r i)).domRestrict
    (J.restrictScalars A)

/-- The completed Jacobian differential kills the square of the presentation ideal.
Source: Stacks Project, restricted.tex, Tags 0AJU and 0AKG
(blueprint: def-per-completed-polynomial-conormal).
Proof: the extension satisfies Leibniz because polynomial approximation modulo every ideal
power reduces that identity to the polynomial Leibniz identity; separatedness then gives
the identity on P. For f,g in J, d(fg) = f*d(g) + g*d(f) lies in J, so its image in P/J
is zero. Every element of J squared is a finite sum of such products. A-linearity and
additivity therefore make the raw map zero on J squared, which is the indicated submodule. -/
theorem rigJacobianRawDifferential_ker_submodule {A : Type u} [CommRing A]
    [IsNoetherianRing A]
    (r : ℕ) (I : Ideal A) (J : Ideal (rigPolynomialCompletion I r)) :
    ((J • (⊤ : Submodule (rigPolynomialCompletion I r) J)).restrictScalars A) ≤
      (LinearMap.pi (fun i : Fin r ↦ rigJacobianRawDifferential r I J i)).ker := by
  sorry

/-- The continuous polynomial Jacobian differential on `J/J²`.
Source: Stacks Project, restricted.tex, Tags 0AJU and 0AKG
(blueprint: def-per-completed-polynomial-conormal).
It is the unique map induced by the raw derivatives because the Leibniz rule makes `J²` vanish
modulo `J`; the well-definedness proof is postponed to stage 3. -/
noncomputable def rigJacobianDifferential {A : Type u} [CommRing A]
    [IsNoetherianRing A] (r : ℕ) (I : Ideal A)
    (J : Ideal (rigPolynomialCompletion I r)) :
    J.Cotangent →ₗ[A]
      (Fin r → (rigPolynomialCompletion I r ⧸ J)) :=
  (((J • (⊤ : Submodule (rigPolynomialCompletion I r) J)).restrictScalars A)).liftQ
    (LinearMap.pi (fun i : Fin r ↦ rigJacobianRawDifferential r I J i))
    (rigJacobianRawDifferential_ker_submodule r I J)

end AlgebraicGeometry
