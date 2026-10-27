/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.LinearAlgebra.Matrix.LeftInverseMinors

/-! # Determinant-open coordinates for the units of a finite algebra

Source: Milne, Algebraic Groups (2017), Proposition 12.60, proof, printed p.250;
the multiplication-matrix argument for any finite commutative algebra
(blueprint: lem-sfb-finite-algebra-units-affine-chart).

For arbitrary test rings the norm must be a unit, including nonreduced and zero rings.
The construction below uses the actual principal open in the polynomial spectrum.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.FiniteAlgebraUnits

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A] {d : ℕ}

/-- The matrix of multiplication by the universal element in the given basis.
Source: Milne, Proposition 12.60, proof, p.250, multiplication-matrix construction
(blueprint: lem-sfb-finite-algebra-units-affine-chart). -/
def multiplicationMatrix (e : Module.Basis (Fin d) k A) :
    Matrix (Fin d) (Fin d) (MvPolynomial (Fin d) k) :=
  fun h j ↦ ∑ i, MvPolynomial.C (e.repr (e i * e j) h) * MvPolynomial.X i

/-- The norm polynomial is the determinant of universal multiplication.
Source: Milne, Proposition 12.60, proof, p.250
(blueprint: lem-sfb-finite-algebra-units-affine-chart). -/
def normPolynomial (e : Module.Basis (Fin d) k A) : MvPolynomial (Fin d) k :=
  (multiplicationMatrix e).det

/-- The principal open whose primes do not contain the norm polynomial.
Source: Milne, Proposition 12.60, proof, p.250
(blueprint: lem-sfb-finite-algebra-units-affine-chart). -/
def openSubset (e : Module.Basis (Fin d) k A) :
    (Spec (.of (MvPolynomial (Fin d) k))).Opens :=
  PrimeSpectrum.basicOpen (normPolynomial e)

/-- The determinant open with its structure morphism to the field spectrum.
Source: Milne, Proposition 12.60, proof, p.250
(blueprint: lem-sfb-finite-algebra-units-affine-chart). -/
def chart (e : Module.Basis (Fin d) k A) : Over (Spec (.of k)) :=
  Over.mk ((openSubset e).ι ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin d) k))))

/-- Evaluation identifies the determinant open with the unit functor, naturally on all
commutative test algebras; its affine representing object is characterized by these maps.
Source: Milne, Proposition 12.60, proof, p.250; multiplication-matrix generalization
(blueprint: lem-sfb-finite-algebra-units-affine-chart).

Proof, following the six steps of the node:
1. The basic open is affine with ring k[x][1/N]
   (lem-weil-pbc-affine-open-section-vanishing-prime). Polynomial evaluation and
   lem-weil-pbc-localization-away-universal-property identify its R-points with tuples
   where N evaluates to a unit, even for the zero ring.
2. By lem-weil-pbc-free-module-base-change-free the e_i tensor 1 form an R-basis.
   Tensor multiplication (lem-weil-pbc-algebra-tensor-pushout-universal-property)
   gives the evaluated multiplication matrix. The determinant finite-sum formula
   (def-weil-pbc-matrix-determinant) commutes with evaluation.
3. A unit gives inverse multiplication matrices; the square case of
   lem-weil-pbc-matrix-left-inverse-minors makes its determinant a unit. Conversely,
   lem-weil-pbc-matrix-adjugate-identity gives an inverse multiplication matrix;
   apply it to the vector of 1 to obtain a multiplicative inverse. Restrict the
   base-changed basis bijection to the two subsets of units.
4. Tensor maps send e_i tensor a_i to e_i tensor phi(a_i). Evaluation and the unique
   localization extensions commute with phi; thus both coordinate equivalences are
   natural, with no reducedness assumption.
5. For another affine representative P, compose its given equivalences inversely with
   these coordinate equivalences. Apply lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection
   to the coordinate algebras. Taking Spec gives an isomorphism over k that induces
   exactly the given equivalences on all affine test schemes.
6. At the coordinates of 1_A the multiplication matrix is the identity. Thus N(b)=1,
   giving a k-point and hence a point of the open. None of the steps requires A to
   be separable or reduced, or R to be reduced. -/
theorem affineChart [Nontrivial A] [FiniteDimensional k A]
    (e : Module.Basis (Fin d) k A) (hd : 0 < d) :
    IsAffine (chart e).left ∧
    (∀ b : Fin d → k, (∑ i, b i • e i) = 1 →
      MvPolynomial.aeval b (normPolynomial e) = 1) ∧
    Nonempty (chart e).left ∧
    ∃ E : ∀ R : CommAlgCat.{u} k,
        (((Spec (.of R)).asOver (Spec (.of k)) ⟶ chart e) ≃
          {a : Fin d → R // IsUnit (MvPolynomial.aeval a (normPolynomial e))}),
    ∃ V : ∀ R : CommAlgCat.{u} k,
        ({a : Fin d → R // IsUnit (MvPolynomial.aeval a (normPolynomial e))} ≃
          (A ⊗[k] R)ˣ),
      (∀ (R : CommAlgCat.{u} k)
          (p : (Spec (.of R)).asOver (Spec (.of k)) ⟶ chart e),
        p.left ≫ (openSubset e).ι =
          Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (E R p).val).toRingHom)) ∧
      (∀ (R : CommAlgCat.{u} k)
          (a : {a : Fin d → R // IsUnit (MvPolynomial.aeval a (normPolynomial e))}),
        (V R a : A ⊗[k] R) = ∑ i, (e i) ⊗ₜ[k] (a.val i)) ∧
      (∀ (R S : CommAlgCat.{u} k) (φ : R ⟶ S)
          (p : (Spec (.of R)).asOver (Spec (.of k)) ⟶ chart e),
        (E S ((Spec.map (CommRingCat.ofHom φ.hom.toRingHom)).asOver _ ≫ p)).val =
          fun i ↦ φ.hom ((E R p).val i)) ∧
      (∀ (R S : CommAlgCat.{u} k) (φ : R ⟶ S)
          (a : {a : Fin d → R // IsUnit (MvPolynomial.aeval a (normPolynomial e))})
          (b : {b : Fin d → S // IsUnit (MvPolynomial.aeval b (normPolynomial e))}),
        b.val = (fun i ↦ φ.hom (a.val i)) →
          V S b = Units.map
            (Algebra.TensorProduct.map (AlgHom.id k A) φ.hom).toMonoidHom (V R a)) ∧
      (∀ (P : Over (Spec (.of k))) [IsAffine P.left]
          (β : ∀ R : CommAlgCat.{u} k,
            (((Spec (.of R)).asOver (Spec (.of k)) ⟶ P) ≃ (A ⊗[k] R)ˣ)),
        (∀ (R S : CommAlgCat.{u} k) (φ : R ⟶ S)
            (p : (Spec (.of R)).asOver (Spec (.of k)) ⟶ P),
          β S ((Spec.map (CommRingCat.ofHom φ.hom.toRingHom)).asOver _ ≫ p) =
            Units.map (Algebra.TensorProduct.map (AlgHom.id k A) φ.hom).toMonoidHom
              (β R p)) →
        ∃ ι : chart e ≅ P,
          ∀ (R : CommAlgCat.{u} k)
              (p : (Spec (.of R)).asOver (Spec (.of k)) ⟶ chart e),
            β R (p ≫ ι.hom) = V R (E R p)) := by
  sorry

end AlgebraicGeometry.FiniteAlgebraUnits
