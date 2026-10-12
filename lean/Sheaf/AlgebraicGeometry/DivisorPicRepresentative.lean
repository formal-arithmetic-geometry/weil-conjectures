/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.DivisorModule
public import WeilConjectures.AlgebraicGeometry.Curve.Picard
import Sheaf.AlgebraicGeometry.DivisorLineBundleAgreesSC
import Sheaf.AlgebraicGeometry.DivisorModuleLocal
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import Sheaf.AlgebraicGeometry.DivisorModuleTensorAdd

/-!
# Comparison of the two divisor-module constructions

Source: blueprint lem-sc-divisor-class-curve, homomorphism step, and
lem-pc-divisor-line-bundle-agrees-sc; Stacks Project, Divisors, Tag 02SL.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem module_invertible
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] (D : C.Divisor) :
    (D.moduleOfSmoothConnectedCurve k C f).IsInvertible := by
  let : IsNoetherian C := isNoetherian_of_locallyOfFiniteType f
  let : IsRegular C := IsRegular.of_smooth f
  let : IsIntegral C := (C.smooth_connected_curve_local_rings k f).choose
  have h := (C.smooth_connected_curve_local_rings k f).choose_spec
  obtain ⟨P, hP⟩ := h.2.2.2.2.2.2.2.1
  let := (h.2.2.2.2.2.2.2.2 P hP).1
  let I := IsLocalRing.maximalIdeal (C.presheaf.stalk P)
  exact (D.module_local k C f ⟨P, hP⟩ (Submodule.IsPrincipal.generator I)
    (Ideal.span_singleton_generator I).symm).2.1

/-- The point-ideal construction of the Picard class of an arbitrary divisor has the
valuation-bounded divisor module as a representative.
Source: blueprint lem-sc-divisor-class-curve, Proof (tensor-product compatibility), and
lem-pc-divisor-line-bundle-agrees-sc, Proof; Stacks Project, Divisors, Tag 02SL
(blueprint: lem-sc-divisor-toPic-representative).

Proof: The local divisor-module theorem gives invertibility of O(E) for every divisor E:
a closed point exists, its stalk is a DVR, and a generator of its maximal ideal supplies
the uniformizer hypothesis. Write D = A - B using its effective positive and negative
parts. For an effective E, lem-pc-divisor-line-bundle-agrees-sc identifies O(E) with the
dual of the point-ideal product I(E). Thus [O(A)] = [I(A)]⁻¹ and [O(B)] = [I(B)]⁻¹.
Tensor compatibility gives [O(D)] [O(B)] = [O(A)], because D + B = A. The formula
Divisor.toMul_toPic_mapRange_sub gives the same product equality for the point-ideal
Picard class of D. Cancel [O(B)] to obtain equality of the two Picard classes, then use
Pic.eq_ofIsInvertible_iff to get the asserted representative isomorphism. This also
handles D = 0, negative divisors, and curves that are not proper; no properness is used. -/
theorem Divisor.nonempty_toPic_iso_module
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [IsConnectedCurve (C ↘ Spec (.of k))] [Smooth (C ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (.of k))] (D : C.Divisor) :
    Nonempty ((fromSkeleton C.Modules).obj (Divisor.toPic k C D).toMul.val ≅
      D.moduleOfSmoothConnectedCurve k C (C ↘ Spec (.of k))) := by
  let M (A : C.Divisor) := A.moduleOfSmoothConnectedCurve k C (C ↘ Spec (.of k))
  have hM (A : C.Divisor) : (M A).IsInvertible :=
    module_invertible k C (C ↘ Spec (.of k)) A
  let E₁ := D.mapRange Int.toNat Int.toNat_zero
  let E₂ := (-D).mapRange Int.toNat Int.toNat_zero
  let A : C.Divisor := E₁.mapRange Nat.cast Nat.cast_zero
  let B : C.Divisor := E₂.mapRange Nat.cast Nat.cast_zero
  have hD : A - B = D := Divisor.mapRange_toNat_sub D
  have hJ₁ := Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k)) E₁
  have hJ₂ := Divisor.isInvertible_idealSheaf (C ↘ Spec (.of k)) E₂
  have := hJ₁.isInvertible_toModules
  have := hJ₂.isInvertible_toModules
  have := hJ₁.isInvertible_dual_toModules
  have := hJ₂.isInvertible_dual_toModules
  have effective (E : closedPoints C →₀ ℕ) :
      Nonempty (Modules.dual (Divisor.idealSheaf E).toModules ≅
        M (E.mapRange Nat.cast Nat.cast_zero)) := by
    have hE : 0 ≤ (E.mapRange Nat.cast Nat.cast_zero : C.Divisor) := by
      intro P
      simp only [Finsupp.mapRange_apply, Finsupp.zero_apply]
      exact Nat.cast_nonneg _
    simpa [Divisor.idealSheaf, Finsupp.prod_mapRange_index, M] using
      divisorLineBundle_agrees_sc k C (C ↘ Spec (.of k))
        (E.mapRange Nat.cast Nat.cast_zero) hE
  obtain ⟨e₁⟩ := effective E₁
  obtain ⟨e₂⟩ := effective E₂
  have := hM D
  have := hM A
  have := hM B
  apply (Pic.eq_ofIsInvertible_iff _ (M D)).mp
  apply mul_right_cancel (b := Pic.ofIsInvertible (M B))
  have hpic := Divisor.toMul_toPic_mapRange_sub (k := k) E₁ E₂
  rw [hD] at hpic
  have h₁ := Pic.ofIsInvertible_eq_of_iso e₁
  have h₂ := Pic.ofIsInvertible_eq_of_iso e₂
  rw [Pic.ofIsInvertible_dual] at h₁ h₂
  rw [hpic, ← h₂, mul_assoc, mul_inv_cancel, mul_one, h₁]
  obtain ⟨e⟩ := Divisor.nonempty_module_tensor_add_iso k C (C ↘ Spec (.of k)) D B
  have hsum : D + B = A := by rw [← hD, sub_add_cancel]
  have heq := Pic.ofIsInvertible_eq_of_iso
    (e ≪≫ eqToIso (congrArg M hsum))
  rw [Pic.ofIsInvertible_tensorObj] at heq
  simpa only [h₂] using heq.symm

end AlgebraicGeometry.Scheme
