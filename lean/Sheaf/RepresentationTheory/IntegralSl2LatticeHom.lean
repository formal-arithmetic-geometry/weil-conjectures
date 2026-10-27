module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Integral SL₂ lattice representations over arbitrary base rings

Source: Milne, Algebraic Groups (2017), Section 23h, equations (152)--(153), pp.509--510;
the functor-of-points convention of lem-sfb-sl2-lattice-integration.
(blueprint: def-sfb-integral-sl2-lattice-hom)

A morphism is a natural family on all algebras, with polynomial matrix entries in a finite
integral basis. Polynomial representatives are precisely functions on
B[a,b,c,d]/(ad-bc-1). The group-homomorphism condition supplies polynomial inverses by
substitution of the adjugate matrix. Thus `regular` expresses representability by a map
from the GL coordinate ring, rather than imposing a condition only on field-valued points.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped TensorProduct

namespace RepresentationTheory

/-- A homomorphism SL₂ over B to GL of a finite free integral lattice after base change.
Every B-algebra, including nonreduced algebras and the zero ring, is tested.
`regular` supplies polynomial representatives of the matrix coefficients; it is a property,
not a choice of representatives in the data of the morphism.
Source: Milne, Section 23h, equations (152)--(153), pp.509--510, and the affine
functor-of-points convention in the integral lattice integration node.
(blueprint: def-sfb-integral-sl2-lattice-hom). -/
structure IntegralSl2LatticeHom (B : Type v) [CommRing B]
    (L : Type u) [AddCommGroup L] [Module ℤ L]
    [Module.Free ℤ L] [Module.Finite ℤ L] where
  /-- The group homomorphism on all algebra-valued points. -/
  app (A : CommAlgCat.{max u v} B) : Matrix.SpecialLinearGroup (Fin 2) A →*
    ((A ⊗[ℤ] L) ≃ₗ[A] (A ⊗[ℤ] L))
  /-- Scalar extension commutes with the action on every vector. -/
  naturality {A C : CommAlgCat.{max u v} B} (f : A ⟶ C)
      (g : Matrix.SpecialLinearGroup (Fin 2) A) (x : A ⊗[ℤ] L) :
    TensorProduct.map f.hom.toRingHom.toAddMonoidHom.toIntLinearMap
        (LinearMap.id : L →ₗ[ℤ] L) (app A g x) =
      app C (Matrix.SpecialLinearGroup.map f.hom.toRingHom g)
        (TensorProduct.map f.hom.toRingHom.toAddMonoidHom.toIntLinearMap
          (LinearMap.id : L →ₗ[ℤ] L) x)
  /-- Polynomial coefficients in some finite integral basis, including the empty basis. -/
  regular : ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ L)
      (p : Matrix (Fin n) (Fin n) (MvPolynomial (Fin 2 × Fin 2) B)),
    ∀ (A : CommAlgCat.{max u v} B) (g : Matrix.SpecialLinearGroup (Fin 2) A)
      (i j : Fin n),
      ((b.baseChange A).repr (app A g ((b.baseChange A) j))) i =
        MvPolynomial.eval₂ (algebraMap B A) (fun q ↦ g q.1 q.2) (p i j)

/-- The diagonal matrix diag(s,s⁻¹), constructed by its root-word formula
w(s)w(1)⁻¹, where w(s) = x₊(s)x₋(-s⁻¹)x₊(s). This works over every ring.
Source: the two-chart rank-one factorization in the integral lattice integration node,
Milne, Section 23h, pp.509--510 (blueprint: def-sfb-integral-sl2-lattice-hom). -/
def integralSl2Diagonal {A : Type v} [CommRing A] (s : Aˣ) :
    Matrix.SpecialLinearGroup (Fin 2) A :=
  (Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (s : A) *
    Matrix.SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (-(↑s⁻¹ : A)) *
    Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (s : A)) *
  (Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (1 : A) *
    Matrix.SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (-1 : A) *
    Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (1 : A))⁻¹

end RepresentationTheory
