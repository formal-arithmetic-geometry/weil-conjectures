/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.AlgebraicGeometry.DiagonalizableGroup
public import Sheaf.AlgebraicGeometry.AdditiveSubgroupPolynomialQuotient
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Finiteness

/-! # Principal additive crossed homomorphisms from smooth diagonalizable groups

Source: Milne, Algebraic Groups (2017), Proposition 15.3, printed p.303, with the
smooth-quotient scope of Summary 16.29, printed p.334
(blueprint: lem-sfb-smooth-diagonal-additive-crossed-vanishing).

The formulas are equalities of affine-test points in the existing additive group.
Membership in the closed subgroup is expressed through its actual inclusion.
Neither connectedness nor smoothness of the additive subgroup is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.StandardGroupSchemes

namespace AlgebraicGeometry

/-- Every regular crossed homomorphism into a scalar-stable closed additive subgroup
is principal, for a smooth diagonalizable source. The witness is an F-point of the
subgroup, and the identity holds on every commutative F-algebra, including nonreduced ones.

Source: Milne, Algebraic Groups (2017), Proposition 15.3, printed p.303;
Summary 16.29, printed p.334
(blueprint: lem-sfb-smooth-diagonal-additive-crossed-vanishing).

Proof plan (the four steps of the DAG node):
1. By lem-sfb-smooth-diagonal-prime-to-characteristic-torsion-density, the groups
   H_n = D[n](F), for n prime to the characteristic (all n in characteristic zero),
   are finite of order c_n prime to that characteristic and detect regular functions.
   Multiplication by c_n is bijective on N(F): divide in F. For N = G_a this is
   immediate; otherwise lem-sfb-additive-subgroup-polynomial-quotient gives an additive
   defining polynomial P. If c_n b = s and P(s) = 0, then c_n P(b) = 0, so P(b) = 0.
   Injectivity is cancellation in F. This uses no smoothness of N.
2. Sum f over H_n, obtaining s_n in N(F). Permuting the sum by y ↦ xy in the crossed
   identity gives s_n = c_n f(x) + chi(x) s_n. Divide by c_n inside N(F) to get a_n
   with f(x) = (1 - chi(x)) a_n on H_n. This fixes the sign of the principal cocycle.
3. If chi is trivial, these formulas give f = 0 on every H_n. Apply the regular-function
   detection in lem-sfb-smooth-diagonal-prime-to-characteristic-torsion-density to the
   pullback of the additive coordinate (def-sc-gm-ga, def-weil-affine-spectrum).
   Thus f is zero on every algebra and the zero point of N is a witness.
4. Otherwise the same detection applied to chi*(t) - 1 gives h in some H_n0 with
   chi(h) ≠ 1. Set a = a_n0. For arbitrary n, use m = lcm(n,n0). Comparing the formulas
   for m and n0 at h gives a_m = a; hence the formula with a holds on every H_n.
   Detection applied to f*(y) - a(1 - chi*(t)) proves equality of regular functions,
   therefore equality on every algebra. Scalar stability and subtraction put the right
   side in N(A), and injectivity of the closed subgroup inclusion gives equality in N.
-/
theorem smooth_diagonal_additive_crossed_principal
    {F : Type u} [Field F] [IsAlgClosed F]
    (D N : Over (Spec (.of F))) [GrpObj D] [GrpObj N]
    [IsAffine D.left] [LocallyOfFiniteType D.hom] [QuasiCompact D.hom]
    [IsAffine N.left] [LocallyOfFiniteType N.hom] [QuasiCompact N.hom]
    [Smooth D.hom]
    (hdiag : ∃ (M : Type u) (_ : AddCommGroup M) (_ : AddGroup.FG M),
      Nonempty (Grp.mk D ≅ diagonalizableGroup F M))
    (chi : D ⟶ multiplicative F) [IsMonHom chi]
    (i : N ⟶ additive F) [IsClosedSubgroupScheme i]
    (hstable : ∀ (A : Type u) [CommRing A] [Algebra F A]
      (d : affine F A ⟶ D) (x : A),
      (∃ z : affine F A ⟶ N, z ≫ i = additiveCoordinatePoint F A x) →
      ∃ z : affine F A ⟶ N, z ≫ i = additiveCoordinatePoint F A
        (multiplicativeCoordinateValue F (d ≫ chi) * x))
    (f : D ⟶ N)
    (hcrossed : ∀ (A : Type u) [CommRing A] [Algebra F A]
      (d d' : affine F A ⟶ D) (x y : A),
      d ≫ f ≫ i = additiveCoordinatePoint F A x →
      d' ≫ f ≫ i = additiveCoordinatePoint F A y →
      (d * d') ≫ f ≫ i = additiveCoordinatePoint F A
        (x + multiplicativeCoordinateValue F (d ≫ chi) * y)) :
    ∃ a : F, (∃ z : affine F F ⟶ N, z ≫ i = additiveCoordinatePoint F F a) ∧
      ∀ (A : Type u) [CommRing A] [Algebra F A] (d : affine F A ⟶ D),
        d ≫ f ≫ i = additiveCoordinatePoint F A
          (algebraMap F A a - multiplicativeCoordinateValue F (d ≫ chi) * algebraMap F A a) := by
  sorry

end AlgebraicGeometry
