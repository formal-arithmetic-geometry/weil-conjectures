/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Standard smoothness of an étale polynomial algebra

An étale algebra over a finite polynomial algebra is standard smooth over the base.

## Implementation details

An étale algebra is standard smooth of relative dimension zero, a polynomial algebra is standard
smooth, and standard smooth maps compose.

## References

* Stacks Project, Algebra, Lemma 00U9; the final paragraph of Lemma 07CH
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- An étale algebra over a finite polynomial algebra is standard smooth over the base. -/
theorem isStandardSmooth_of_etale_polynomial
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B] (n : ℕ)
    (θ : MvPolynomial (Fin n) R →ₐ[R] B)
    (hθ : @Etale (MvPolynomial (Fin n) R) B _ _ θ.toRingHom.toAlgebra) :
    IsStandardSmooth R B := by
  let instPB : Algebra (MvPolynomial (Fin n) R) B := θ.toRingHom.toAlgebra
  have : @IsScalarTower R (MvPolynomial (Fin n) R) B _ instPB.toSMul _ :=
    IsScalarTower.of_algHom θ
  have : Etale (MvPolynomial (Fin n) R) B := hθ
  have : IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin n) R) B :=
    Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  have : IsStandardSmooth (MvPolynomial (Fin n) R) B :=
    IsStandardSmoothOfRelativeDimension.isStandardSmooth 0
  have : IsStandardSmooth R (MvPolynomial (Fin n) R) :=
    IsStandardSmooth.of_basis_kaehlerDifferential
      (KaehlerDifferential.mvPolynomialBasis R (Fin n)) (by
        rintro _ ⟨i, rfl⟩
        exact ⟨MvPolynomial.X i, by simp⟩)
  exact IsStandardSmooth.trans R (MvPolynomial (Fin n) R) B

end Algebra
