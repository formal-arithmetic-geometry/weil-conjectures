module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Basic
import WeilConjectures.RingTheory.GradedAlgebra.Standard
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.CharP.Defs

/-! # Linearization of split-torus actions on vector groups

Source: Conrad--Lichtenstein, Linear Algebraic Groups I, Appendix D.3, proof of
Theorem D.3.2, printed pp.86--87; Milne, Algebraic Groups (2017), Example 14.40
and Proposition 14.50 (blueprint: lem-sfb-torus-vector-group-linearization).

We use W = k^d. Its vector group is the categorical product of d copies of the
recorded additive group, with its actual additive group law. Its scalar extension
has coordinates R^d. The general linear group is the existing affine group scheme,
not the abstract group of its k-points. Equivariance is expressed in coordinates
on every commutative k-algebra. The isomorphism a can change additive polynomial
coordinates; no initial linear structure on C is assumed to be preserved.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- The i-th coordinate of an R-point of Ga^d, obtained by its product projection
and evaluation of the coordinate of the recorded additive affine line.
Source: Milne, Example 14.40, pp.292--293; Conrad--Lichtenstein, Appendix D.3, p.86
(blueprint: lem-sfb-torus-vector-group-linearization). -/
def additivePowerPointCoordinate (k : Type u) [Field k] (d : ℕ)
    {R : Type u} [CommRing R] [Algebra k R]
    (x : StandardGroupSchemes.affine k R ⟶
      (∏ᶜ fun _ : Fin d ↦ Grp.mk (StandardGroupSchemes.additive k)).X)
    (i : Fin d) : R :=
  (Scheme.ΓSpecIso (.of R)).hom
    ((x ≫ (Pi.π (fun _ : Fin d ↦
      Grp.mk (StandardGroupSchemes.additive k)) i).hom.hom).left.appTop
        ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X))

/-- Every algebraic split-torus action by group automorphisms on a vector group
becomes linear after a group-scheme change of additive coordinates. Here W = k^d,
so GL(W) is the existing GL_d, and the displayed finite sum is its action on
W tensor R = R^d. Equivalently, its matrix coordinate functions give the linear
coaction W -> W tensor O(E); the group-homomorphism identities are exactly the
coassociativity and counit identities. No restriction on characteristic is made.

Source: Conrad--Lichtenstein, Appendix D.3, proof of Theorem D.3.2, pp.86--87
(blueprint: lem-sfb-torus-vector-group-linearization).

Proof:
1. Pull the action back through any isomorphism Ga^d -> C. The space P of additive
   polynomials is graded by total degree. The degree-zero part vanishes. Apply
   lem-trf-additive-polynomial-monomial-classification degree by degree: in
   characteristic zero P has basis x_i; in characteristic p it has basis x_i^(p^r).
   In the latter case P is free of rank d over k_sigma[F], where F acts by p-th
   powers and (a F^r)(b F^t) = a b^(p^r) F^(r+t).
2. Write the action coaction on each additive polynomial as a finite Laurent sum.
   Comparing Laurent coefficients in the additive identity shows each coefficient
   is additive. Coassociativity makes these coefficients weight vectors; the counit
   recovers their sum. Thus P is the direct sum of its lattice weight spaces.
3. In characteristic zero P is already the span of x_i, so the original coordinates
   give a matrix representation. Acting by the inverse torus element inverts each
   matrix, and the action identities give a morphism of group schemes into GL_d.
4. In characteristic p, Frobenius carries weight nu to p nu. Apply
   lem-sfb-torus-equivariant-frobenius-module-basis to get an A-basis f_j of P
   consisting of weight vectors, over the original field without perfectness.
5. The additive polynomial map b = (f_j) has an additive polynomial inverse v:
   express each x_i in the A-basis f_j. The two basis-change matrices compose to
   the identity, and multiplication in A is composition of additive polynomials.
   These are polynomial identities, hence hold over every test algebra.
6. Put a = b_0 composed with v and let rho have diagonal Laurent monomials given
   by the weights. The weight identities imply b(e.x) = rho(e)b(x), giving the
   displayed coordinate formula. The Laurent Hopf identities give the equivalent
   coaction identities. Empty coordinates handle d = 0; s = 0 gives trivial action.
-/
theorem torus_vectorGroup_linearization (k : Type u) [Field k] (d s : ℕ)
    (C : Grp (Over (Spec (.of k))))
    [IsAffine C.X.left] [LocallyOfFiniteType C.X.hom] [QuasiCompact C.X.hom]
    (hC : Nonempty ((∏ᶜ fun _ : Fin d ↦
      Grp.mk (StandardGroupSchemes.additive k)) ≅ C))
    (action : ModObj (MultiplicativeType.splitTorus k s).X C.X)
    (hAut : ∀ (R : Type u) [CommRing R] [Algebra k R]
      (e : StandardGroupSchemes.affine k R ⟶ (MultiplicativeType.splitTorus k s).X)
      (x y : StandardGroupSchemes.affine k R ⟶ C.X),
      lift e (x * y) ≫ action.smul =
        (lift e x ≫ action.smul) * (lift e y ≫ action.smul)) :
    ∃ (a : (∏ᶜ fun _ : Fin d ↦ Grp.mk (StandardGroupSchemes.additive k)) ≅ C)
      (ρ : (MultiplicativeType.splitTorus k s).X ⟶
        GeneralLinearGroup (ULift.{u} (Fin d)) k),
      IsMonHom ρ ∧
      ∀ (R : Type u) [CommRing R] [Algebra k R]
        (e : StandardGroupSchemes.affine k R ⟶ (MultiplicativeType.splitTorus k s).X)
        (x : StandardGroupSchemes.affine k R ⟶ C.X) (i : Fin d),
        additivePowerPointCoordinate k d
            ((lift e x ≫ action.smul) ≫ a.inv.hom.hom) i =
          ∑ j : Fin d,
            (GeneralLinearGroup.homMulEquiv (ULift.{u} (Fin d)) k R (e ≫ ρ)).val
                ⟨i⟩ ⟨j⟩ *
              additivePowerPointCoordinate k d (x ≫ a.inv.hom.hom) j := by
  sorry

end AlgebraicGeometry
