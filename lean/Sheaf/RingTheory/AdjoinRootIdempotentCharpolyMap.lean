/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.LinearAlgebra.IdempotentCharpoly
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Coprime.Basic

/-! # Reduction of determinant polynomials on the two CRT summands

Source: Stacks Project, Tag 09XI, proof of (3)⇒(1), reduction of characteristic polynomials.
(blueprint: lem-weil-pbc-adjoinRoot-idempotent-charpoly-map)
-/

@[expose] public section

universe u

namespace Polynomial

/-- The determinant polynomials reduce to the two prescribed CRT factors.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1).
(blueprint: lem-weil-pbc-adjoinRoot-idempotent-charpoly-map)

Proof: the power basis of the monic quotient is compatible with scalar extension
A→A/I, giving the quotient by the mapped polynomial. By the coprime factorization,
Chinese remainders identify it with the product of the quotients by g₀ and h₀.
Multiplication by the class of X becomes multiplication by X on both factors, and
the two residue hypotheses make multiplication by e the projection (1,0).
Multiplication by 1-e is its complementary projection. In the concatenation of the
power bases of the two quotients, `1-P+(X-T)P` is block diagonal with the
characteristic matrix for multiplication by X on the first factor and the identity
on the second. Its determinant is g₀, since the characteristic polynomial of
multiplication by X on a monic quotient is its defining polynomial. The complementary
projection gives h₀ in the same way. Determinants commute with coefficient reduction
and are invariant under change of basis, so these equalities hold for the original
power-basis matrices. For the zero quotient ring every polynomial equality holds;
for degree-zero factors the corresponding block is empty and its determinant is one.
No Jacobson hypothesis or idempotence before reduction is needed for this calculation. -/
theorem adjoinRoot_idempotentCharpoly_map
    {A : Type u} [CommRing A] (I : Ideal A)
    (f : A[X]) (hf : f.Monic) (g₀ h₀ : (A ⧸ I)[X])
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcoprime : IsCoprime g₀ h₀)
    (hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀)
    (e : AdjoinRoot f)
    (he₁ : AdjoinRoot.map (Ideal.Quotient.mk I) f g₀
      (hfactor.symm ▸ dvd_mul_right g₀ h₀) e = 1)
    (he₀ : AdjoinRoot.map (Ideal.Quotient.mk I) f h₀
      (hfactor.symm ▸ dvd_mul_left h₀ g₀) e = 0) :
    let b := (AdjoinRoot.powerBasis' hf).basis;
    let T := Algebra.leftMulMatrix b (AdjoinRoot.root f);
    let P := Algebra.leftMulMatrix b e;
    (Matrix.idempotentCharpoly T P).map (Ideal.Quotient.mk I) = g₀ ∧
      (Matrix.idempotentCharpoly T (1 - P)).map (Ideal.Quotient.mk I) = h₀ := by
  sorry

end Polynomial
