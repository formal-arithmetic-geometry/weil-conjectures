/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.HopfCoactionLinearization
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.Nat.Factorial.Basic

/-! # Polynomial lower-root orbits of SL2 highest vectors

Source: Milne, Algebraic Groups (2017), Propositions 22.14--22.17, printed pp.466--467,
and the SL2 root datum in 22.33 (blueprint: lem-sfb-sl2-highest-orbit-polynomial).

The given module is the existing counital coassociative coordinate comodule. Point values
are obtained by evaluating the coefficient factor, with the node's M tensor R order.
Matrix points use the existing special linear group scheme.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

universe u

open CategoryTheory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.SL2HighestOrbit

variable {k : Type u} [Field k]

/-- Expose the already defined special linear group law on its underlying k-scheme.
Source: Milne, 22.33 (blueprint: lem-sfb-sl2-highest-orbit-polynomial). -/
instance underlyingGroup :
    GrpObj ((LinearGroupSchemes.specialLinear k 2).left.asOver (Spec (.of k))) :=
  LinearGroupSchemes.specialGroup k 2

/-- The existing special linear scheme is the spectrum of its determinant-one quotient.
Source: Milne, 22.33 (blueprint: lem-sfb-sl2-highest-orbit-polynomial). -/
instance underlyingAffine : IsAffine (LinearGroupSchemes.specialLinear k 2).left :=
  inferInstanceAs (IsAffine (Spec (.of (LinearGroupSchemes.SpecialAlgebra k 2))))

/-- The upper root matrix I + a E12, with universe-lifted matrix indices.
Source: Milne, 22.33 (blueprint: lem-sfb-sl2-highest-orbit-polynomial). -/
def upper {R : Type u} [CommRing R] (a : R) :
    Matrix.SpecialLinearGroup (LinearGroupSchemes.Index.{u} 2) R :=
  Matrix.SpecialLinearGroup.transvection
    (i := ULift.up (0 : Fin 2)) (j := ULift.up (1 : Fin 2))
    (fun h ↦ zero_ne_one (congrArg ULift.down h)) a

/-- The lower root matrix I + a E21.
Source: Milne, 22.33 (blueprint: lem-sfb-sl2-highest-orbit-polynomial). -/
def lower {R : Type u} [CommRing R] (a : R) :
    Matrix.SpecialLinearGroup (LinearGroupSchemes.Index.{u} 2) R :=
  Matrix.SpecialLinearGroup.transvection
    (i := ULift.up (1 : Fin 2)) (j := ULift.up (0 : Fin 2))
    (fun h ↦ one_ne_zero (congrArg ULift.down h)) a

/-- The diagonal matrix diag(t,t inverse), written as a product of root matrices:
upper(t) lower(-t inverse) upper(t) upper(-1) lower(1) upper(-1).
Multiplying the first three factors gives rows (0,t),(-t inverse,0); the last three
have rows (0,-1),(1,0), so their product is the specified diagonal over every algebra.
Source: Milne, 22.33 (blueprint: lem-sfb-sl2-highest-orbit-polynomial). -/
def torus {R : Type u} [CommRing R] (t : Rˣ) :
    Matrix.SpecialLinearGroup (LinearGroupSchemes.Index.{u} 2) R :=
  upper (t : R) * lower (-(t⁻¹ : Rˣ) : R) * upper (t : R) *
    upper (-1 : R) * lower (1 : R) * upper (-1 : R)

/-- Evaluate the given coordinate coaction at the specified determinant-one matrix.
The coordinate map is Spec.mapMulEquiv inverse after the canonical isoSpec map and
specialPoints; tensor evaluation is real data and is the rational point action on z tensor 1.
Source: Milne, Remark 4.1 and 22.33
(blueprint: lem-sfb-sl2-highest-orbit-polynomial). -/
def act {M : Type u} [AddCommGroup M] [Module k M]
    (c : {c : M →ₗ[k] M ⊗[k] Γ((LinearGroupSchemes.specialLinear k 2).left, ⊤) //
      HopfAction.Coassociative k Γ((LinearGroupSchemes.specialLinear k 2).left, ⊤) M c ∧
      HopfAction.Counital k Γ((LinearGroupSchemes.specialLinear k 2).left, ⊤) M c})
    (R : Type u) [CommRing R] [Algebra k R]
    (g : Matrix.SpecialLinearGroup (LinearGroupSchemes.Index.{u} 2) R) :
    M →ₗ[k] M ⊗[k] R :=
  (((Spec.mapMulEquiv (R := k)
    (S := Γ((LinearGroupSchemes.specialLinear k 2).left, ⊤)) (T := R)).symm
      ((LinearGroupSchemes.specialPoints k 2 R).symm g ≫
        (LinearGroupSchemes.specialLinear k 2).left.isoSpec.hom.asOver
          (Spec (.of k)))).ofConv.toLinearMap.lTensor M) ∘ₗ c.val

/-- A highest vector has a unique lower-root orbit polynomial of degree at most m,
with factorial coefficients; below the positive characteristic it is a truncated exponential.
Source: Milne, Propositions 22.14--22.17, pp.466--467, and 22.33; the factorial
recurrence is obtained from the lower-root addition law over dual numbers.
(blueprint: lem-sfb-sl2-highest-orbit-polynomial).

Proof:
1. Substitute the polynomial lower-root matrix into the given coordinate coaction of v.
   This gives a finite polynomial P(T) with vector coefficients w_j, whose evaluations
   give the lower-root orbit over every algebra. Likewise expand Q(S) = upper(S) n v,
   where n has rows (0,-1),(1,0).
2. Direct matrix multiplication gives lower(T) = upper(T inverse) n torus(T)
   upper(T inverse) over k[T,T inverse]. The upper-root invariance and torus-weight
   hypotheses imply P(T) = T^m Q(T inverse). Comparing Laurent coefficients makes
   every coefficient in degree greater than m zero, without a simplicity assumption.
3. The polynomial-to-Laurent map remains injective after tensoring with M: use a basis
   of M. Hence the truncated identity holds before localization and evaluates at every
   a, including nonunits. Evaluation at zero gives w_0 = v. Any second family gives
   the same polynomial by testing R = k[T], a = T, so coefficient comparison proves
   uniqueness, including zero coefficients at the upper end.
4. In k[T,epsilon]/epsilon squared, lower(T+epsilon) = lower(epsilon) lower(T).
   The defining dual-number identity for f and comparison of epsilon T^j coefficients
   yield f(w_j) = (j+1) w_(j+1) for j < m, and f(w_m) = 0. No integer is divided out.
5. Induction gives f^j v = j! w_j for j at most m, starting with f^0 v = v = 0! w_0.
   If the characteristic p is positive and m < p, each factor in j! is nonzero in k,
   including the empty product for j = 0. Thus j! is a unit; solve for w_j and
   substitute in the orbit identity. These are precisely the five steps of the node.
-/
theorem existsUnique_orbit_coefficients
    [IsAlgClosed k] {M : Type u} [AddCommGroup M] [Module k M]
    [FiniteDimensional k M]
    (c : {c : M →ₗ[k] M ⊗[k] Γ((LinearGroupSchemes.specialLinear k 2).left, ⊤) //
      HopfAction.Coassociative k Γ((LinearGroupSchemes.specialLinear k 2).left, ⊤) M c ∧
      HopfAction.Counital k Γ((LinearGroupSchemes.specialLinear k 2).left, ⊤) M c})
    (m : ℕ) (v : M) (hv : v ≠ 0)
    (hupper : ∀ (R : Type u) [CommRing R] [Algebra k R] (a : R),
      act c R (upper a) v = v ⊗ₜ[k] (1 : R))
    (htorus : ∀ (R : Type u) [CommRing R] [Algebra k R] (t : Rˣ),
      act c R (torus t) v = v ⊗ₜ[k] ((t : R) ^ m))
    (f : Module.End k M)
    (hf : ∀ z : M,
      act c (DualNumber k) (lower DualNumber.eps) z =
        z ⊗ₜ[k] (1 : DualNumber k) + f z ⊗ₜ[k] DualNumber.eps) :
    ∃! w : Fin (m + 1) → M,
      (∀ (R : Type u) [CommRing R] [Algebra k R] (a : R),
        act c R (lower a) v = ∑ j, w j ⊗ₜ[k] (a ^ j.val)) ∧
      w 0 = v ∧
      (∀ j : Fin (m + 1), (f ^ j.val) v = (j.val.factorial : k) • w j) ∧
      ∀ (p : ℕ) [CharP k p], 0 < p → m < p →
        (∀ j : Fin (m + 1), IsUnit (j.val.factorial : k)) ∧
        ∀ (R : Type u) [CommRing R] [Algebra k R] (a : R),
          act c R (lower a) v =
            ∑ j : Fin (m + 1),
              (f ^ j.val) v ⊗ₜ[k] (a ^ j.val * algebraMap k R (j.val.factorial : k)⁻¹) := by
  sorry

end AlgebraicGeometry.SL2HighestOrbit

