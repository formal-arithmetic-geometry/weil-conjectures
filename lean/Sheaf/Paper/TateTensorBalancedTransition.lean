/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.TateTensorFiniteTransitionData

/-! The ordinary square between the root-power map and the integral quotient tower.

Source: smooth-purity transport, normalized Tate tower, Step 4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

/-- A map of ordinary finite root tensors with the root-power formula agrees with
the transition of the ordinary integral quotient tower after balanced identifications.
This is an identity of sheaf maps; no derived functor or adic tower appears.

Source: smooth-purity transport, normalized Tate tower, Step 4, ordinary quotient
balancing. (blueprint: lem-pur-tate-tensor-balanced-transition)

Proof: the adjacent strict quotient transition sends t tensor x to q(t) tensor x,
by localReductionStep_exists. Induct on b-a to obtain this formula for every
comparable pair, using the quotient cocycle, with the identity at equal indices.
Check the proposed square locally on scalar multiples of finite pure root tensors.
Lift their roots, after a pro-etale covering, to compatible integral root families;
such lifts exist since ell is invertible. The upper and lower projections of one
family are related by the power map, which is r.roots by roots_power and monicity
of the root inclusion. Apply ProjectionBalanced at b and a and the assumed formula
for f. Both composites send t times the finite tensor with scalar s to
q(t) times scalars_a(phi(s)) tensor the integral generator. The equality of scalars
is scalars_comp. Local tensor generation, the site comparison adjunction and the
associated-module sheafification unit show that these elements locally span the
source; hence the two sheaf maps agree. For d=0 this is coefficient multiplication,
and the proof also includes empty schemes and zero sections. -/
theorem tateTensor_balanced_transition
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d b a : ℕ) (hab : a ≤ b)
    (r : CoefficientLineComparison
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
      (ell ^ (b + 1)) (ell ^ (a + 1))
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)
    (f : (pbcRestrict (pbcAdicProjection T (datum.{u} ell) b)).obj
        ((realization T ell b).obj (finiteSheaf T ell b d)) ⟶
      (pbcRestrict (pbcAdicProjection T (datum.{u} ell) a)).obj
        ((realization T ell a).obj (finiteSheaf T ell a d)))
    (hf : FiniteRootTransition T ell d b a hab r f)
    (cb : (realization T ell b).obj (finiteSheaf T ell b d) ≅ quotientLine T ell b d)
    (ca : (realization T ell a).obj (finiteSheaf T ell a d) ≅ quotientLine T ell a d)
    (hb : ProjectionBalanced T ell b d cb) (ha : ProjectionBalanced T ell a d ca) :
    f ≫ (pbcRestrict (pbcAdicProjection T (datum.{u} ell) a)).map ca.hom =
      (pbcRestrict (pbcAdicProjection T (datum.{u} ell) b)).map cb.hom ≫
        (strictTower T ell d).map (homOfLE hab).op := by sorry

end AlgebraicGeometry.Scheme.PurityIntegralTower
