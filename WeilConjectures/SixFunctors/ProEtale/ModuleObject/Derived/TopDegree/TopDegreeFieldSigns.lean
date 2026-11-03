/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopDegree.TopDegreeTraceDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupSigns.TraceCupSigns
import Mathlib.Algebra.CharP.Defs
import all Mathlib.Logic.Small.Defs
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # The signed consequences of the perfect Koszul pairing

Source: sk-cor-trace, complement (iii), proof step 12.
(blueprint: lem-pd-field-pairing-sign-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing.TopDegree
open PurityTransport
variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)

/-- Perfectness and the single Koszul symmetry equation imply all the signed
field clauses, including the middle sign and characteristic-zero alternation.
Source: complement (iii), step 12 (blueprint: lem-pd-field-pairing-sign-assembly).
Proof: i(2d-i) has the parity of i. Specialize to i=d for the middle sign.
For odd d the diagonal value is its negative; in characteristic zero the scalar
2 is nonzero in the coefficient field, so that value is zero. -/
theorem fieldPairing_of_perfect_of_symmetry {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (h : ∀ _hF : IsField (CategoryTheory.MonObj.Γ (c.obj.{u} ell)),
      (∀ i : ℤ, ∃ b : H ell c X i →ₗ[CategoryTheory.MonObj.Γ (c.obj.{u} ell)]
          H ell c X (2 * (d : ℤ) - i) →ₗ[CategoryTheory.MonObj.Γ (c.obj.{u} ell)]
            Value ell c k d,
        (∀ x y, b x y = pairing ell c hEll X d i x y) ∧
          Function.Bijective b ∧ Function.Bijective b.flip) ∧
      (∀ (i : ℤ) (x : H ell c X i) (y : H ell c X (2 * (d : ℤ) - i)),
        pairing ell c hEll X d (2 * (d : ℤ) - i) y
            ((eqToHom (congrArg (H ell c X) (by omega : i = 2 * (d : ℤ) -
              (2 * (d : ℤ) - i)))) x) =
          sign (i * (2 * (d : ℤ) - i)) • pairing ell c hEll X d i x y)) :
    FieldPairing ell c hEll X d := by
  intro hF
  obtain ⟨hp, hs⟩ := h hF
  have hsign (i : ℤ) : sign (i * (2 * (d : ℤ) - i)) = sign i :=
    congrArg Units.val (TraceCupSigns.complement (d : ℤ) i)
  have hm (x y : H ell c X (d : ℤ)) :
      pairing ell c hEll X d (d : ℤ) y
          ((eqToHom (congrArg (H ell c X) (by omega : (d : ℤ) = 2 * (d : ℤ) - d))) x) =
        ((-1 : ℤ) ^ d) • pairing ell c hEll X d (d : ℤ) x
          ((eqToHom (congrArg (H ell c X) (by omega : (d : ℤ) = 2 * (d : ℤ) - d))) y) := by
    have hi := hs (d : ℤ) x
      ((eqToHom (congrArg (H ell c X) (by omega : (d : ℤ) = 2 * (d : ℤ) - d))) y)
    have hmiddle : sign ((d : ℤ) * (2 * (d : ℤ) - d)) = (-1 : ℤ) ^ d :=
      TraceCupSigns.middle d
    rw [hmiddle] at hi
    have hd : 2 * (d : ℤ) - d = (d : ℤ) := by omega
    have ht (j : ℤ) (hj : j = (d : ℤ)) (he : (d : ℤ) = 2 * (d : ℤ) - j) :
        pairing ell c hEll X d j
            ((eqToHom (congrArg (H ell c X) hj.symm)) y)
            ((eqToHom (congrArg (H ell c X) he)) x) =
          pairing ell c hEll X d (d : ℤ) y
            ((eqToHom (congrArg (H ell c X)
              (by omega : (d : ℤ) = 2 * (d : ℤ) - d))) x) := by
      subst j
      simp only [eqToHom_refl, ModuleCat.id_apply]
    rw [ht _ hd (by omega)] at hi
    exact hi
  refine ⟨hp, ?_, hm, ?_⟩
  · intro i x y
    exact ⟨hs i x y, congrArg (fun n : ℤ ↦ n • pairing ell c hEll X d i x y) (hsign i)⟩
  · intro hchar hd x
    let R := CategoryTheory.MonObj.Γ (c.obj.{u} ell)
    let : Field R := hF.toField
    let : CharZero R := (CharP.ringChar_zero_iff_CharZero R).mp hchar
    have hskew := hm x x
    rw [hd.neg_one_pow, neg_one_zsmul] at hskew
    exact TraceCupSigns.eq_zero_of_eq_neg (R := R) hskew

end AlgebraicGeometry.ProEtale.CondensedRing.TopDegree
