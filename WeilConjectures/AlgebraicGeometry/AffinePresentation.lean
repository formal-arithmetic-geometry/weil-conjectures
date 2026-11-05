/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RingHom.StandardSmooth

/-! # Affine presentations of schemes of finite type over a field

We collect elementary scheme-theoretic and commutative-algebra facts about affine schemes of
finite type over a field `k₀`:

* every affine `k₀`-scheme of finite type is isomorphic over `Spec k₀` to the spectrum of a
  quotient of a polynomial ring `k₀[X₀, …, X_{n-1}]`;
* the projection `Spec (k₀[X₀, …, Xₙ] ⧸ I) ⟶ 𝔸ⁿ` forgetting the last coordinate, and the
  description of its fibres over `k₀`-points as spectra of quotients of `k₀[X]`;
* finiteness of `Spec (k₀[X] ⧸ J)` for `J ≠ ⊥` and smoothness of `𝔸¹`;
* descent of Frobenius-fixed points of affine schemes over a finite field.
-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial

namespace AlgebraicGeometry

section SpecIso

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

end SpecIso

section Presentation

variable {k₀ : Type u} [Field k₀]

end Presentation

section BaseCases

variable {k₀ : Type u} [Field k₀]

/-- The polynomial algebra `R[X₀, …, X_{n-1}]` is standard smooth of relative dimension `n`
over `R`. -/
lemma isStandardSmoothOfRelativeDimension_mvPolynomial (R : Type u) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  let v : PEmpty.{1} → MvPolynomial (Fin n) R := PEmpty.elim
  let P : Algebra.PreSubmersivePresentation R
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range v)) (Fin n) PEmpty.{1} :=
    .naive PEmpty.elim (fun a ↦ a.elim)
  let Q : Algebra.SubmersivePresentation R _ (Fin n) PEmpty.{1} :=
    { P with jacobian_isUnit := by simp [P.jacobian_eq_jacobiMatrix_det] }
  let e : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range v)) ≃ₐ[R] MvPolynomial (Fin n) R :=
    (Ideal.quotientEquivAlgOfEq R (by simp [v])).trans (AlgEquiv.quotientBot R _)
  exact (Q.ofAlgEquiv e).isStandardSmoothOfRelativeDimension
    (by simp [Algebra.Presentation.dimension])

end BaseCases

section Projection

variable {k₀ : Type u} [Field k₀] {n : ℕ}

variable {T : Type*} [CommRing T]

end Projection

section Frobenius

end Frobenius

end AlgebraicGeometry
