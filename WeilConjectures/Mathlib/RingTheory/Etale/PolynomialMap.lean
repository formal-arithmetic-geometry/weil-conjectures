/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The polynomial map `z ↦ P(x)`

Let `P ∈ R[X]` be monic of positive degree and let `φ : R[z] ⟶ R[X]`, `z ↦ P`, be the
`R`-algebra map, with `R[z] = MvPolynomial PUnit R`. Then `R[X] = R[z][Y] / (P(Y) - z)`, so

- `φ` is finite (`Polynomial.Monic.finite_aeval_pUnit`): `X` is a root of the monic polynomial
  `P(Y) - z` over `R[z]`;
- `φ` is étale away from the zeros of `P'` (`Polynomial.Monic.etale_aeval_pUnit`): the
  localization `R[X][1/P']` is the standard étale `R[z]`-algebra `R[z][Y][1/P'(Y)] / (P(Y) - z)`.
-/

@[expose] public section

open Polynomial

universe u

namespace Polynomial

variable {R : Type u} [CommRing R]

/-- The polynomial `P(Y) - z` over `R[z] = MvPolynomial PUnit R`: its roots in an `R[z]`-algebra
are the preimages of `z` under the polynomial map `x ↦ P(x)`. -/
noncomputable def subPUnitX (P : R[X]) : (MvPolynomial PUnit.{u + 1} R)[X] :=
  P.map MvPolynomial.C - C (MvPolynomial.X PUnit.unit)

lemma monic_subPUnitX {P : R[X]} (hP : P.Monic) (hdeg : 0 < P.natDegree) :
    (subPUnitX P).Monic := by
  have : Nontrivial R := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    simp [Subsingleton.elim P 0] at hdeg
  refine (hP.map _).sub_of_left (degree_C_le.trans_lt ?_)
  rw [degree_map_eq_of_leadingCoeff_ne_zero _ (by simp [hP.leadingCoeff])]
  exact natDegree_pos_iff_degree_pos.mp hdeg

lemma aeval_subPUnitX (P : R[X]) {S : Type*} [CommRing S]
    [Algebra (MvPolynomial PUnit.{u + 1} R) S] (x : S) :
    aeval x (subPUnitX P) =
      eval₂ ((algebraMap (MvPolynomial PUnit.{u + 1} R) S).comp
        (MvPolynomial.C (σ := PUnit.{u + 1}) (R := R))) x P -
        algebraMap (MvPolynomial PUnit.{u + 1} R) S (MvPolynomial.X PUnit.unit) := by
  simp [subPUnitX, aeval_def, eval₂_map]

variable (P : R[X])

/-- If `P` is monic of positive degree, then `R[z] ⟶ R[X]`, `z ↦ P`, is finite. -/
theorem Monic.finite_aeval_pUnit (hP : P.Monic) (hdeg : 0 < P.natDegree) :
    (MvPolynomial.aeval (R := R) fun _ : PUnit.{u + 1} ↦ P).toRingHom.Finite := by
  let _ : Algebra (MvPolynomial PUnit.{u + 1} R) R[X] :=
    (MvPolynomial.aeval fun _ : PUnit.{u + 1} ↦ P).toRingHom.toAlgebra
  have hC : (algebraMap (MvPolynomial PUnit.{u + 1} R) R[X]).comp
      (MvPolynomial.C (σ := PUnit.{u + 1}) (R := R)) = C := by
    ext r
    simp [RingHom.algebraMap_toAlgebra]
  have hX : IsIntegral (MvPolynomial PUnit.{u + 1} R) (X : R[X]) := by
    refine ⟨subPUnitX P, monic_subPUnitX hP hdeg, ?_⟩
    rw [← aeval_def, aeval_subPUnitX, hC, eval₂_C_X]
    simp [RingHom.algebraMap_toAlgebra]
  have hadj : Algebra.adjoin (MvPolynomial PUnit.{u + 1} R) {(X : R[X])} = ⊤ := by
    rw [eq_top_iff]
    rintro a -
    induction a using Polynomial.induction_on with
    | C r =>
      rw [← hC]
      exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => exact add_mem hp hq
    | monomial n r _ =>
      rw [← hC]
      exact mul_mem (Subalgebra.algebraMap_mem _ _)
        (pow_mem (Algebra.subset_adjoin (Set.mem_singleton _)) _)
  have : Module.Finite (MvPolynomial PUnit.{u + 1} R) R[X] := ⟨by
    rw [← Algebra.top_toSubmodule, ← hadj]
    exact hX.fg_adjoin_singleton⟩
  exact this

/-- If `P` is monic of positive degree, then `R[z] ⟶ R[X][1/P']`, `z ↦ P`, is étale: the
target is the standard étale algebra `R[z][Y][1/P'(Y)] / (P(Y) - z)`. -/
theorem Monic.etale_aeval_pUnit (hP : P.Monic) (hdeg : 0 < P.natDegree) :
    ((algebraMap R[X] (Localization.Away (derivative P))).comp
      (MvPolynomial.aeval (R := R) fun _ : PUnit.{u + 1} ↦ P).toRingHom).Etale := by
  let _ : Algebra (MvPolynomial PUnit.{u + 1} R) R[X] :=
    (MvPolynomial.aeval fun _ : PUnit.{u + 1} ↦ P).toRingHom.toAlgebra
  set B := MvPolynomial PUnit.{u + 1} R
  set L := Localization.Away (derivative P)
  have hC : (algebraMap B R[X]).comp (MvPolynomial.C (σ := PUnit.{u + 1}) (R := R)) = C := by
    ext r
    simp [B, RingHom.algebraMap_toAlgebra]
  have hXP : algebraMap B R[X] (MvPolynomial.X PUnit.unit) = P := by
    simp [B, RingHom.algebraMap_toAlgebra]
  have hBL : (algebraMap B L).comp (MvPolynomial.C (σ := PUnit.{u + 1}) (R := R)) =
      (algebraMap R[X] L).comp C := by
    rw [IsScalarTower.algebraMap_eq B R[X] L, RingHom.comp_assoc, hC]
  have hBL' : (algebraMap R[X] L).comp
      (MvPolynomial.aeval (R := R) fun _ : PUnit.{u + 1} ↦ P).toRingHom = algebraMap B L :=
    (IsScalarTower.algebraMap_eq B R[X] L).symm
  rw [hBL', RingHom.etale_algebraMap]
  let Q : StandardEtalePair B :=
    ⟨subPUnitX P, monic_subPUnitX hP hdeg, derivative (subPUnitX P), 1, 0, 1, by simp⟩
  have hg : Q.g = (derivative P).map (MvPolynomial.C (σ := PUnit.{u + 1}) (R := R)) := by
    dsimp only [Q]
    rw [subPUnitX, derivative_sub, derivative_map, derivative_C, sub_zero]
  set x : L := algebraMap R[X] L X
  have hx : Q.HasMap x := by
    refine ⟨?_, ?_⟩
    · rw [aeval_subPUnitX, hBL, ← hom_eval₂, eval₂_C_X, IsScalarTower.algebraMap_apply B R[X] L,
        hXP, sub_self]
    · rw [hg, aeval_def, eval₂_map, hBL, ← hom_eval₂, eval₂_C_X]
      exact IsLocalization.Away.algebraMap_isUnit _
  -- the inverse `R[X][1/P'] ⟶ R[z][Y][1/P'(Y)] / (P(Y) - z)`, `X ↦ Y`
  set c := (algebraMap B Q.Ring).comp (MvPolynomial.C (σ := PUnit.{u + 1}) (R := R))
  let σ : R[X] →+* Q.Ring := eval₂RingHom c Q.X
  have hσ : IsUnit (σ (derivative P)) := by
    have h := Q.hasMap_X.2
    rwa [hg, aeval_def, eval₂_map] at h
  let τ : L →+* Q.Ring := IsLocalization.Away.lift (derivative P) hσ
  have hτ (p : R[X]) : τ (algebraMap R[X] L p) = σ p := IsLocalization.lift_eq _ _
  have hτB : τ.comp (algebraMap B L) = algebraMap B Q.Ring := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun _ ↦ ?_)
    · rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply B R[X] L, hτ]
      simp [σ, c, B, RingHom.algebraMap_toAlgebra]
    · have h := Q.hasMap_X.1
      rw [aeval_subPUnitX, sub_eq_zero] at h
      rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply B R[X] L, hXP, hτ]
      exact h
  let τA : L →ₐ[B] Q.Ring := { τ with commutes' := fun b ↦ congr($hτB b) }
  have hτA (p : R[X]) : τA (algebraMap R[X] L p) = σ p := hτ p
  refine Algebra.Etale.of_equiv (AlgEquiv.ofAlgHom (Q.lift x hx) τA ?_ ?_)
  · refine AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (Submonoid.powers
      (derivative P)) (Polynomial.ringHom_ext (fun r ↦ ?_) ?_))
    · simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, AlgHom.comp_apply, AlgHom.id_apply]
      rw [hτA]
      simp only [σ, c, coe_eval₂RingHom, eval₂_C, RingHom.comp_apply, AlgHom.commutes]
      rw [IsScalarTower.algebraMap_apply B R[X] L]
      simp [B, RingHom.algebraMap_toAlgebra]
      rfl
    · simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, AlgHom.comp_apply, AlgHom.id_apply]
      rw [hτA]
      simp [σ]
      rfl
  · refine StandardEtalePair.hom_ext ?_
    rw [AlgHom.comp_apply, StandardEtalePair.lift_X, hτA]
    simp [σ]

end Polynomial
