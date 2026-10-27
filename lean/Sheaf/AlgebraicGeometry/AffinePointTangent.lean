/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import WeilConjectures.Mathlib.RingTheory.Ideal.Cotangent
public import WeilConjectures.Mathlib.Algebra.DualNumber
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Basis.Defs

/-! # Positive character weights at an affine fixed point

Source: Milne, Algebraic Groups (2017), Section 13e, pp.267--270,
especially Definition 13.40 and Theorem 13.41
(blueprint: def-sfb-affine-point-positive-tangent-weights).

Cotangent spaces are Mathlib's ideal quotients. Their duals are converted to
actual dual-number points by the existing `AlgHom.toDualNumber` construction.
The weight condition is tested over every algebra, using the given scheme action.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped MonObj

namespace AlgebraicGeometry.AffinePointTangent

variable {F A : Type u} [Field F] [CommRing A] [Algebra F A]

/-- The scalar extension of the tangent vector, as an actual dual-number point.
Source: Milne, Section 13e, p.267, and the cotangent interpretation of the tangent space
(blueprint: def-sfb-affine-point-positive-tangent-weights). -/
def pointOver (ε : A →ₐ[F] F) (v : (RingHom.ker ε).Cotangent →ₗ[F] F)
    (R : Type u) [CommRing R] [Algebra F R] :
    StandardGroupSchemes.affine F (DualNumber R) ⟶ StandardGroupSchemes.affine F A :=
  StandardGroupSchemes.map F ((DualNumber.mapAlgebraMap R).comp (ε.toDualNumber v))

/-- Positive integer character weights on the tangent space at an affine rational point.
A finite homogeneous basis implements the direct sum of weight subspaces. The displayed
identity is on dual-number points over every algebra, not on differentials of characters.
Source: Milne, Definition 13.40 and Theorem 13.41, pp.269--270
(blueprint: def-sfb-affine-point-positive-tangent-weights). -/
def HasPositiveWeights (ε : A →ₐ[F] F)
    [ModObj (StandardGroupSchemes.multiplicative F) (StandardGroupSchemes.affine F A)] :
    Prop :=
  ∃ (d : ℕ) (b : Module.Basis (Fin d) F ((RingHom.ker ε).Cotangent →ₗ[F] F))
    (n : Fin d → ℕ), (∀ i : Fin d, 0 < n i) ∧
      ∀ (R : Type u) [CommRing R] [Algebra F R]
        (g : StandardGroupSchemes.affine F R ⟶ StandardGroupSchemes.multiplicative F)
        (i : Fin d),
        (StandardGroupSchemes.map F (TrivSqZeroExt.inlAlgHom F R R) ≫ g) •
            pointOver ε (b i) R =
          StandardGroupSchemes.map F
              ((DualNumber.scale
                (((algSpec.fullyFaithful (R := .of F)).preimage g).unop.hom
                  (LaurentPolynomial.T 1) ^ n i)).restrictScalars F) ≫
            pointOver ε (b i) R

end AlgebraicGeometry.AffinePointTangent
