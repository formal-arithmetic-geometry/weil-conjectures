module

public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.DualNumber
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Primitive-weight rigidity from right logarithmic derivatives

Source: agent auxiliary argument in the setting of Conrad, Reductive group schemes,
Proposition 5.1.16 and Section 6.2, Step 3, pp.147--148, 207.
(blueprint: lem-sfb-primitive-weight-logarithmic-rigidity).

The logarithmic derivatives are actual dual-number points. Equivariance and additivity
are tested on all commutative base algebras, including nonreduced algebras.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped MonObj

namespace AlgebraicGeometry

/-- The polynomial-coordinate point used in the ordered chart and its test-algebra formulas.
It is the spectrum of evaluation, fixing coefficients.
Source: the coordinate construction in the agent auxiliary argument for Conrad,
Proposition 5.1.16 (blueprint: lem-sfb-primitive-weight-logarithmic-rigidity). -/
noncomputable def primitiveWeightPoint (A : Type u) [CommRing A]
    (I : Type u) (R : Type u) [CommRing R] [Algebra A R] (z : I → R) :
    (algSpec (.of A)).obj (op (CommAlgCat.of A R)) ⟶
      (algSpec (.of A)).obj (op (CommAlgCat.of A (MvPolynomial I A))) :=
  (algSpec (.of A)).map (CommAlgCat.ofHom (MvPolynomial.aeval z)).op

/-- Evaluation of the monomial character e_m at an algebra-valued torus point.
Full faithfulness recovers the unique coordinate algebra map of the specified point.
Source: Conrad, Appendix B.1, in the agent auxiliary argument
(blueprint: lem-sfb-primitive-weight-logarithmic-rigidity). -/
noncomputable def primitiveWeightCharacter (A : Type u) [CommRing A]
    (M : Type u) [AddCommGroup M] (R : Type u) [CommRing R] [Algebra A R]
    (t : (algSpec (.of A)).obj (op (CommAlgCat.of A R)) ⟶
      (ringDiagonalizableGroup A M).X) (m : M) : R :=
  ((algSpec.fullyFaithful (R := .of A)).preimage
    (X := op (CommAlgCat.of A R))
    (Y := op (CommAlgCat.of A (AddMonoidAlgebra A M))) t).unop.hom
      (AddMonoidAlgebra.single m 1)

/-- The fixed ordered multiplication map from the polynomial coordinate chart.
The list order, rather than a commutative product, is used even when H is noncommutative.
Source: Conrad, Proposition 5.1.16, in the agent auxiliary argument
(blueprint: lem-sfb-primitive-weight-logarithmic-rigidity). -/
noncomputable def primitiveWeightOrderedProduct (A : Type u) [CommRing A]
    (H : Grp (Over (Spec (.of A)))) (J : Type u) [Fintype J]
    (e : Fin (Fintype.card J) ≃ J)
    (p : J → ((algSpec (.of A)).obj (op (CommAlgCat.of A (MvPolynomial PUnit.{u + 1} A))) ⟶ H.X)) :
    (algSpec (.of A)).obj (op (CommAlgCat.of A (MvPolynomial J A))) ⟶ H.X :=
  (List.ofFn fun q : Fin (Fintype.card J) =>
    (algSpec (.of A)).map (CommAlgCat.ofHom
      (MvPolynomial.aeval (fun _ : PUnit.{u + 1} => MvPolynomial.X (e q)))).op ≫ p (e q)).prod

/-- The right logarithmic derivative in direction d as a dual-number point:
F(z+epsilon e_d) F(z)^{-1}. DualNumber is B[epsilon]/(epsilon^2), with its actual
constant inclusion and coefficient projections; equality here is equality of tangent points.
Source: the dual-number cancellation step of the agent auxiliary argument for Conrad,
Section 6.2, Step 3 (blueprint: lem-sfb-primitive-weight-logarithmic-rigidity). -/
noncomputable def primitiveWeightLogDerivative (A : Type u) [CommRing A]
    (H : Grp (Over (Spec (.of A))))
    (F : (algSpec (.of A)).obj (op (CommAlgCat.of A (MvPolynomial (ULift.{u} (Fin 2)) A))) ⟶ H.X)
    (d : Fin 2) :
    (algSpec (.of A)).obj (op (CommAlgCat.of A (DualNumber (MvPolynomial (ULift.{u} (Fin 2)) A)))) ⟶
      H.X :=
  (primitiveWeightPoint A (ULift.{u} (Fin 2)) (DualNumber (MvPolynomial (ULift.{u} (Fin 2)) A))
    (fun q => TrivSqZeroExt.inlAlgHom A _ _ (MvPolynomial.X q) +
      if q.down = d then DualNumber.eps else 0) ≫ F) *
    (primitiveWeightPoint A (ULift.{u} (Fin 2)) (DualNumber (MvPolynomial (ULift.{u} (Fin 2)) A))
      (fun q => TrivSqZeroExt.inlAlgHom A _ _ (MvPolynomial.X q)) ≫ F)⁻¹

/-- Equivariant maps with equal right logarithmic derivatives agree when the ordered
additive coordinates have distinct primitive bidegrees. No restriction on the characteristic,
torsion or nilpotents is imposed; the coordinate set may be empty. Integer-relation
independence of r,s is equivalent to rational independence in the finite free lattice M.

Source: agent auxiliary argument in the root-coordinate setting of Conrad,
Proposition 5.1.16 and Section 6.2, Step 3, pp.147--148, 207
(blueprint: lem-sfb-primitive-weight-logarithmic-rigidity).

Proof plan (the six steps of the node):
1. Write Phi for the ordered product and K=F0^{-1}F1. The action by automorphisms
makes K equivariant. The weight identity makes Phi and its inverse equivariant. Pulling
back the coordinate variables along Phi^{-1}K gives polynomials f_j, by the affine-spectrum
adjunction (lem-a1-locally-ringed-space-affine-adjunction) and polynomial universality
(def-weil-pbc-mv-polynomial-ring).
2. If d is the common right logarithmic derivative, the shifted points are d*u and d*v.
Hence their quotient is (d*u)^{-1}(d*v)=u^{-1}v. Apply this in both directions.
3. Pull back every coordinate: f_j(z+epsilon e_d)=f_j(z). Expand monomials using epsilon^2=0
and compare epsilon coefficients; both partial derivatives vanish
(def-weil-pbc-polynomial-partial-derivative).
4. Equivariance at the universal torus point and the e_m basis of the group algebra
(def-sfb-ring-diagonalizable-group) force f_j=C_j*x^(i_j)*y^(k_j). Indeed a nonzero
coefficient of x^a*y^b requires a*r+b*s=i_j*r+k_j*s; independence forces a=i_j,b=k_j.
5. Vanishing partials give i_j*C_j=k_j*C_j=0, also when an exponent is zero. Integer
Bezout for the coprime exponents gives u*i_j+v*k_j=1 and therefore C_j=0. For completeness,
Bezout follows by taking the least positive element of i_j*Z+k_j*Z and applying division
with remainder: it divides both exponents and hence their gcd 1. No integer is inverted.
6. All chart coordinates vanish. Polynomial universality and the affine adjunction give
K=Phi(0)=1, since each additive homomorphism takes 0 to 1. Thus F0=F1. For empty J,
Phi identifies H with Spec A and the same coordinate uniqueness has no coordinates. -/
theorem primitiveWeight_logarithmic_rigidity
    (A : Type u) [CommRing A] [Nontrivial A]
    (M : Type u) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (r s : M) (hrs : ∀ a b : ℤ, a • r + b • s = 0 → a = 0 ∧ b = 0)
    (J : Type u) [Fintype J] (i k : J → ℕ)
    (hprimitive : ∀ j : J, Nat.Coprime (i j) (k j))
    (hdistinct : Function.Injective (fun j : J => i j • r + k j • s))
    (H : Grp (Over (Spec (.of A)))) [Smooth H.X.hom] [IsAffineHom H.X.hom]
    [ModObj (ringDiagonalizableGroup A M).X H.X]
    (hautomorphisms : ∀ (U : Over (Spec (.of A)))
      (t : U ⟶ (ringDiagonalizableGroup A M).X) (g h : U ⟶ H.X),
      t • (g * h) = (t • g) * (t • h))
    (p : J → ((algSpec (.of A)).obj (op (CommAlgCat.of A (MvPolynomial PUnit.{u + 1} A))) ⟶ H.X))
    (hclosed : ∀ j : J, IsClosedImmersion (p j).left)
    (hadditive : ∀ (R : Type u) [CommRing R] [Algebra A R] (j : J) (a b : R),
      (primitiveWeightPoint A PUnit.{u + 1} R (fun _ => a + b) ≫ p j) =
        (primitiveWeightPoint A PUnit.{u + 1} R (fun _ => a) ≫ p j) *
          (primitiveWeightPoint A PUnit.{u + 1} R (fun _ => b) ≫ p j))
    (e : Fin (Fintype.card J) ≃ J) (hchart : IsIso (primitiveWeightOrderedProduct A H J e p))
    (hweight : ∀ (R : Type u) [CommRing R] [Algebra A R]
      (t : (algSpec (.of A)).obj (op (CommAlgCat.of A R)) ⟶
        (ringDiagonalizableGroup A M).X) (j : J) (z : R),
      t • (primitiveWeightPoint A PUnit.{u + 1} R (fun _ => z) ≫ p j) =
        primitiveWeightPoint A PUnit.{u + 1} R
          (fun _ => primitiveWeightCharacter A M R t (i j • r + k j • s) * z) ≫ p j)
    (F0 F1 : (algSpec (.of A)).obj
      (op (CommAlgCat.of A (MvPolynomial (ULift.{u} (Fin 2)) A))) ⟶ H.X)
    (horigin0 : primitiveWeightPoint A (ULift.{u} (Fin 2)) A (fun _ => 0) ≫ F0 = 1)
    (horigin1 : primitiveWeightPoint A (ULift.{u} (Fin 2)) A (fun _ => 0) ≫ F1 = 1)
    (hequivariant : ∀ (F : (algSpec (.of A)).obj
      (op (CommAlgCat.of A (MvPolynomial (ULift.{u} (Fin 2)) A))) ⟶ H.X),
      F = F0 ∨ F = F1 → ∀ (R : Type u) [CommRing R] [Algebra A R]
        (t : (algSpec (.of A)).obj (op (CommAlgCat.of A R)) ⟶
          (ringDiagonalizableGroup A M).X) (z : ULift.{u} (Fin 2) → R),
        t • (primitiveWeightPoint A (ULift.{u} (Fin 2)) R z ≫ F) =
          primitiveWeightPoint A (ULift.{u} (Fin 2)) R
            (fun q => primitiveWeightCharacter A M R t (if q.down = 0 then r else s) * z q) ≫ F)
    (hx : primitiveWeightLogDerivative A H F0 0 = primitiveWeightLogDerivative A H F1 0)
    (hy : primitiveWeightLogDerivative A H F0 1 = primitiveWeightLogDerivative A H F1 1) :
    F0 = F1 := by
  sorry

end AlgebraicGeometry
