/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.RingTheory.EtalePolynomialCertificate
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.TensorProduct.Maps
import Sheaf.Paper.DirectedColimitBaseChangeElementwise
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Descent of finite polynomial inverse certificates

Source: Stacks Project, Algebra, proof of Tag 07RI, descent of inverse identities.
(blueprint: lem-weil-pbc-etale-polynomial-certificate-colimit).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

/-- A finite polynomial inverse certificate for fixed relations descends to a stage.
This concerns polynomial equations and ideal memberships, and makes no assertion
about etaleness or about a presented target algebra.

Source: Stacks Project, Algebra, proof of Tag 07RI, lines 47654-47662.
(blueprint: lem-weil-pbc-etale-polynomial-certificate-colimit).

Proof: expand each membership in the relation ideal as a sum e_klj f_j, and each
membership in its square as a sum h_jab f_a f_b. There are finitely many polynomials
c, e and h in finitely many variables. Polynomial scalar extension identifies the
coefficient-base-changed polynomial algebra with T tensor P₀, where
P₀ = B₀[x₁,...,x_n]. Elementwise tensor-colimit descent represents every one of
these polynomials at a stage. Directedness places these representatives together
above i₀. Coefficientwise transition maps preserve f_j and commute with partial
derivatives. Thus the finitely many differences between the two sides of the
expanded equations map to zero at the colimit. Elementwise eventual vanishing
and directedness kill all these differences at one later stage. The resulting
c, e and h give the two required ideal memberships there. When either finite
index set is empty, no coefficients or equations need lifting; i₀ suffices for
an empty list and the same construction handles the remaining equations. -/
theorem exists_stage_etalePolynomialCertificate
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F] (i₀ : I)
    (B₀ : Type v) [CommRing B₀] [Algebra (F.obj i₀) B₀]
    (n m : ℕ) (f : Fin m → MvPolynomial (Fin n) B₀) :
    letI : Algebra (F.obj i₀) (colimit F : CommRingCat.{u}) :=
      (colimit.ι F i₀).hom.toAlgebra
    EtalePolynomialCertificate
      (fun j ↦ MvPolynomial.map
        (Algebra.TensorProduct.includeRight.toRingHom :
          B₀ →+* (colimit F : CommRingCat.{u}) ⊗[F.obj i₀] B₀) (f j)) →
    ∃ (i : I) (hi : i₀ ≤ i),
      letI : Algebra (F.obj i₀) (F.obj i) := (F.map (homOfLE hi)).hom.toAlgebra
      EtalePolynomialCertificate
        (fun j ↦ MvPolynomial.map
          (Algebra.TensorProduct.includeRight.toRingHom :
            B₀ →+* F.obj i ⊗[F.obj i₀] B₀) (f j)) := by
  sorry

end Algebra
