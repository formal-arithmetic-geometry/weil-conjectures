/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.RingTheory.EtalePolynomialCertificate
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.TensorProduct.Maps
import Sheaf.RingTheory.EtaleRingMapConormalCriterion
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # A uniform polynomial certificate for etaleness of a base-changed presentation

Source: Stacks Project, Algebra, proof of Tag 07RI, presentation and inverse differential.
(blueprint: lem-weil-pbc-etale-base-change-polynomial-certificate).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace AlgebraicGeometry

/-- A finite presentation has fixed finite relations whose base changes characterize
etaleness by a finite polynomial inverse certificate.

Source: Stacks Project, Algebra, proof of Tag 07RI, lines 47640-47661.
(blueprint: lem-weil-pbc-etale-base-change-polynomial-certificate).

Proof: choose a surjective B₀-algebra map from a polynomial algebra with finitely
many variables to C₀, and finitely many generators f of its kernel, using finite
presentation for the B₀-algebra structure induced by φ₀. Tensor cancellation,
polynomial scalar extension and tensor-quotient base change identify each tensor
map with the quotient by the coefficientwise images of these same f. Apply the
conormal criterion to this presentation. For a bijective differential choose
preimages of the finitely many dx_k and express them as sums c_jk f_j modulo J².
The right inverse identity is the first certificate family, by the Leibniz rule.
Injectivity applied to each generating relation class gives the second family.
Conversely the sums c_jk f_j define a linear map from the free differential module
into J/J². The two families check its right inverse on the free basis and its left
inverse on the generating relation classes, respectively. Both composites are
therefore identities, so the conormal differential is bijective and the quotient
map is etale. This includes n = 0, m = 0 and the zero ring: empty sums and the
zero conormal/free modules give exactly the same two inverse conditions. -/
theorem exists_etale_baseChange_polynomialCertificate
    {A₀ : Type u} [CommRing A₀]
    (B₀ C₀ : Type v) [CommRing B₀] [CommRing C₀]
    [Algebra A₀ B₀] [Algebra A₀ C₀]
    (φ₀ : B₀ →ₐ[A₀] C₀) (hfp : φ₀.FinitePresentation) :
    ∃ (n m : ℕ) (f : Fin m → MvPolynomial (Fin n) B₀),
      ∀ (T : Type u) [CommRing T] [Algebra A₀ T],
        Etale (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map (AlgHom.id A₀ T) φ₀).toRingHom)) ↔
        Algebra.EtalePolynomialCertificate
          (fun j ↦ MvPolynomial.map
            (Algebra.TensorProduct.includeRight.toRingHom : B₀ →+* T ⊗[A₀] B₀) (f j)) := by
  sorry

end AlgebraicGeometry
