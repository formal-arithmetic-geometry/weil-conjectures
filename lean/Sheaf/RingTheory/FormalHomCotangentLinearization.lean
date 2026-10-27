/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Data.Matrix.Mul
import WeilConjectures.RingTheory.PowerSeriesQuadraticIdeal

/-!
# Cotangent coefficient bases and linearization of formal algebra maps

Source: Stacks Project, Curves, Tag 0C4B, lemma-fitting-ideal-well-defined,
the final coordinate-change paragraph and its omitted invertible-Jacobian details.
(blueprint: lem-trf-formal-hom-cotangent-linearization).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace MvPowerSeries

/-- The row-convention matrix of linear coefficients of the images of the variables.
Source: Stacks Project, Curves, Tag 0C4B, final coordinate-change paragraph.
(blueprint: lem-trf-formal-hom-cotangent-linearization). -/
noncomputable def linearCoefficientMatrix {F : Type u} [Field F] {m n : ℕ}
    (ψ : MvPowerSeries (Fin m) F →ₐ[F] MvPowerSeries (Fin n) F) :
    Matrix (Fin m) (Fin n) F :=
  fun i j ↦ coeff (Finsupp.single j 1) (ψ (X i))

/-- Coefficients identify the variable ideals modulo their squares with coordinate
spaces, and every algebra homomorphism preserving those ideals acts by its matrix
of linear coefficients. These quotient maps and matrices respect composition and
identity. The numbers of variables may be zero; no continuity is assumed.

Source: Stacks Project, Curves, Tag 0C4B, lemma-fitting-ideal-well-defined,
final coordinate-change paragraph, expanded cotangent linearization details.
(blueprint: lem-trf-formal-hom-cotangent-linearization).

Proof:
1. The Cauchy product gives c(fg) = c(f)c(g) and
   l_i(fg) = c(f)l_i(g) + l_i(f)c(g). Thus the variable ideal has zero constant
   coefficient, and its square has zero constant and linear coefficients.
2. For every h subtract its constant and linear terms. The remainder has zero
   constant and linear coefficients, so mem_span_X_sq_of_coeff_eq_zero places it
   in the square of the variable ideal. This identifies the variable ideal with
   the kernel of c. On its cotangent quotient, coefficient extraction has inverse
   v ↦ [sum_i v_i X_i], is linear, and sends [X_i] to the standard basis vector.
   Apply this construction to both the source and the target.
3. Since h - c(h) lies in the source ideal and ψ fixes F and preserves the ideals,
   c(ψ(h)) = c(h). Multiplicativity gives preservation of their squares. Mathlib's
   Ideal.mapCotangent is therefore the induced F-linear map [h] ↦ [ψ(h)].
4. Apply ψ to h = sum_i l_i(h) X_i + q with q in the square. Its image of q has
   zero linear coefficients, giving the displayed coefficient sum and row formula.
5. On a representative both composite quotient maps send [h] to [θ(ψ(h))].
   Apply step 4 to ψ(X_i) and θ to obtain the (i,k) entry of the matrix product.
   The coefficients of the variables give the identity matrix. Empty variable
   sets give zero ideals, zero cotangent quotients and empty sums and matrices. -/
theorem formal_hom_cotangent_linearization (F : Type u) [Field F] (m n : ℕ)
    (ψ : MvPowerSeries (Fin m) F →ₐ[F] MvPowerSeries (Fin n) F)
    (hψ : Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) F)) ≤
      (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F))).comap ψ) :
    ∃ (eS : (Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) F))).Cotangent
        ≃ₗ[F] (Fin m → F))
      (eT : (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F))).Cotangent
        ≃ₗ[F] (Fin n → F)),
      (∀ h : Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) F)),
        eS ((Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) F))).toCotangent h)
          = fun i ↦ coeff (Finsupp.single i 1) (h : MvPowerSeries (Fin m) F)) ∧
      (∀ h : Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F)),
        eT ((Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F))).toCotangent h)
          = fun j ↦ coeff (Finsupp.single j 1) (h : MvPowerSeries (Fin n) F)) ∧
      (∀ i : Fin m,
        eS ((Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) F))).toCotangent
          ⟨X i, Ideal.subset_span ⟨i, rfl⟩⟩) = Pi.single i 1) ∧
      (∀ j : Fin n,
        eT ((Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F))).toCotangent
          ⟨X j, Ideal.subset_span ⟨j, rfl⟩⟩) = Pi.single j 1) ∧
      (∀ h : MvPowerSeries (Fin m) F, constantCoeff (ψ h) = constantCoeff h) ∧
      (∀ v : (Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) F))).Cotangent,
        eT (Ideal.mapCotangent
          (Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) F)))
          (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F))) ψ hψ v) =
            Matrix.vecMul (eS v) (linearCoefficientMatrix ψ)) ∧
      (∀ h : Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) F)), ∀ j : Fin n,
        coeff (Finsupp.single j 1) (ψ h) =
          ∑ i : Fin m, coeff (Finsupp.single i 1) (h : MvPowerSeries (Fin m) F) *
            linearCoefficientMatrix ψ i j) ∧
      (∀ (r : ℕ) (θ : MvPowerSeries (Fin n) F →ₐ[F] MvPowerSeries (Fin r) F)
        (hθ : Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F)) ≤
          (Ideal.span (Set.range (X : Fin r → MvPowerSeries (Fin r) F))).comap θ),
        Ideal.mapCotangent
          (Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) F)))
          (Ideal.span (Set.range (X : Fin r → MvPowerSeries (Fin r) F)))
          (θ.comp ψ) (fun h hh ↦ hθ (hψ hh)) =
            (Ideal.mapCotangent
              (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F)))
              (Ideal.span (Set.range (X : Fin r → MvPowerSeries (Fin r) F))) θ hθ).comp
              (Ideal.mapCotangent
                (Ideal.span (Set.range (X : Fin m → MvPowerSeries (Fin m) F)))
                (Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) F))) ψ hψ) ∧
        linearCoefficientMatrix (θ.comp ψ) =
          linearCoefficientMatrix ψ * linearCoefficientMatrix θ) ∧
      linearCoefficientMatrix (AlgHom.id F (MvPowerSeries (Fin m) F)) =
        (1 : Matrix (Fin m) (Fin m) F) := by
  sorry

end MvPowerSeries
