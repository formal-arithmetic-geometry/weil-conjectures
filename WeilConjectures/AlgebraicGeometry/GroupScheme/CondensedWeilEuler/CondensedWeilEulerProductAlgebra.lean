/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedDerived.CondensedScalarDerivedLocalFrobenius
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Complex.Basic
public import Mathlib.Order.KrullDimension
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.PowerSeries.Trunc
import WeilConjectures.PointCount
public import WeilConjectures.ZetaLinearAlgebra.AlternatingEulerProduct

/-! # Formal algebra of the condensed Euler product

Source: the coefficientwise argument in Steps 2, 5 and 6 of the Euler-product proof
(blueprint: lem-condensed-weil-euler-formal-algebra).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilEuler
open WeilConjectures.NativeCondensedModule

private theorem determinantFactor_of_isZero {R : Type v} [Field R]
    (V : ModuleCat.{u + 1} R) (F : End V) (e : ℕ) (hV : IsZero V) :
    determinantFactor V F e = 1 := by
  have : Subsingleton V := ModuleCat.isZero_iff_subsingleton.mp hV
  have : Module.Finite R V := inferInstance
  simp [determinantFactor, LinearMap.charpolyRev_of_subsingleton]

private theorem determinantFactor_constantCoeff {R : Type v} [Field R]
    (V : ModuleCat.{u + 1} R) (F : End V) {e : ℕ} (he : 0 < e) :
    PowerSeries.constantCoeff (determinantFactor V F e) = 1 := by
  classical
  unfold determinantFactor
  split_ifs with h
  · let := h
    simp [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.eval_comp, zero_pow (Nat.ne_of_gt he)]
  · simp

private theorem determinantFactor_congr_one {R : Type v} [Field R]
    (V : ModuleCat.{u + 1} R) (F : End V) {e : ℕ} (he : 0 < e) :
    (PowerSeries.X : PowerSeries R) ^ e ∣ determinantFactor V F e - 1 := by
  classical
  rw [PowerSeries.X_pow_dvd_iff]
  intro n hn
  unfold determinantFactor
  split_ifs with h
  · let := h
    rw [map_sub, Polynomial.coeff_coe]
    rw [← Polynomial.expand_eq_comp_X_pow, Polynomial.coeff_expand he]
    by_cases hn0 : n = 0
    · subst n
      simp
    · have hnd : ¬e ∣ n := fun hdiv ↦
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdiv).not_gt hn
      simp [hnd, PowerSeries.coeff_one, hn0]
  · simp

private theorem inverse_congr_one {R : Type v} [Field R] (f : PowerSeries R)
    {e : ℕ} (hf : PowerSeries.constantCoeff f = 1)
    (he : (PowerSeries.X : PowerSeries R) ^ e ∣ f - 1) :
    (PowerSeries.X : PowerSeries R) ^ e ∣ f⁻¹ - 1 := by
  have hi : f⁻¹ * f = 1 := PowerSeries.inv_mul_cancel f (by rw [hf]; exact one_ne_zero)
  have hid : f⁻¹ - 1 = -(f⁻¹ * (f - 1)) := by
    rw [mul_sub, hi, mul_one]
    ring
  rw [hid]
  exact dvd_neg.mpr (dvd_mul_of_dvd_right he _)

private theorem prod_congr_one {R : Type v} [Field R] {I : Type w}
    (s : Finset I) (f : I → PowerSeries R) (e : ℕ)
    (hf : ∀ i ∈ s, (PowerSeries.X : PowerSeries R) ^ e ∣ f i - 1) :
    (PowerSeries.X : PowerSeries R) ^ e ∣ (∏ i ∈ s, f i) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hid : f a * (∏ i ∈ s, f i) - 1 =
        f a * ((∏ i ∈ s, f i) - 1) + (f a - 1) := by ring
    rw [hid]
    exact dvd_add (dvd_mul_of_dvd_right
      (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))) _)
      (hf a (Finset.mem_insert_self a s))

private theorem inverseAlternating_eq_prod {R : Type v} [Field R]
    (V : ℤ → ModuleCat.{u + 1} R) (F : ∀ j, End (V j)) (e : ℕ)
    (S : Finset ℤ) (hS : ∀ j, j ∉ S → IsZero (V j)) :
    inverseAlternating V F e =
      ∏ j ∈ S, if Even j then (determinantFactor (V j) (F j) e)⁻¹
        else determinantFactor (V j) (F j) e := by
  classical
  apply finprod_eq_prod_of_mulSupport_subset
  intro j hj
  by_contra hjS
  have hj1 := determinantFactor_of_isZero (V j) (F j) e (hS j hjS)
  simp [Function.mem_mulSupport, hj1] at hj

private theorem map_inverse {R : Type v} {S : Type w} [Field R] [Field S]
    (f : R →+* S) (P : PowerSeries R) (hP : PowerSeries.constantCoeff P = 1) :
    PowerSeries.map f P⁻¹ = (PowerSeries.map f P)⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hP, map_one]
    exact one_ne_zero)).mpr
  rw [← map_mul, PowerSeries.inv_mul_cancel P (by rw [hP]; exact one_ne_zero), map_one]

private theorem prod_congr_mod {R : Type v} [Field R] {I : Type w}
    (s : Finset I) (f g : I → PowerSeries R) (e : ℕ)
    (hf : ∀ i ∈ s, (PowerSeries.X : PowerSeries R) ^ e ∣ f i - g i) :
    (PowerSeries.X : PowerSeries R) ^ e ∣ (∏ i ∈ s, f i) - ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hid : f a * (∏ i ∈ s, f i) - g a * (∏ i ∈ s, g i) =
        f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) +
          (f a - g a) * (∏ i ∈ s, g i) := by ring
    rw [hid]
    exact dvd_add (dvd_mul_of_dvd_right
      (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))) _)
      (dvd_mul_of_dvd_left (hf a (Finset.mem_insert_self a s)) _)

private theorem coeff_eq_of_congr_mod {R : Type v} [Field R]
    {f g : PowerSeries R} {e n : ℕ}
    (h : (PowerSeries.X : PowerSeries R) ^ e ∣ f - g) (hn : n < e) :
    PowerSeries.coeff n f = PowerSeries.coeff n g := by
  have hc := PowerSeries.X_pow_dvd_iff.mp h n hn
  simpa only [map_sub, sub_eq_zero] using hc

private theorem finiteDegree (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (n : ℕ) : Set.Finite {x : ClosedPoint D X₀ | localClosedPointDegree D X₀ x ≤ n} := by
  have h := X₀.hom.finite_setOf_degreeOver_le n
  rw [X₀.hom.finitePoints_eq_closedPoints] at h
  exact h

private theorem degree_pos (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    (x : ClosedPoint D X₀) : 0 < localClosedPointDegree D X₀ x := by
  have hx : x.val ∈ X₀.left.finitePoints := by
    rw [X₀.hom.finitePoints_eq_closedPoints]
    exact x.property
  exact Nat.pos_of_ne_zero (X₀.hom.degreeOver_ne_zero hx)

private theorem inverseAlternating_constantCoeff {R : Type v} [Field R]
    (V : ℤ → ModuleCat.{u + 1} R) (F : ∀ j, End (V j)) {e : ℕ} (he : 0 < e)
    (S : Finset ℤ) (hS : ∀ j, j ∉ S → IsZero (V j)) :
    PowerSeries.constantCoeff (inverseAlternating V F e) = 1 := by
  classical
  rw [inverseAlternating_eq_prod V F e S hS, map_prod]
  apply Finset.prod_eq_one
  intro j hj
  split_ifs <;> simp [determinantFactor_constantCoeff (V j) (F j) he]

private theorem inverseAlternating_congr_one {R : Type v} [Field R]
    (V : ℤ → ModuleCat.{u + 1} R) (F : ∀ j, End (V j)) {e : ℕ} (he : 0 < e)
    (S : Finset ℤ) (hS : ∀ j, j ∉ S → IsZero (V j)) :
    (PowerSeries.X : PowerSeries R) ^ e ∣ inverseAlternating V F e - 1 := by
  classical
  rw [inverseAlternating_eq_prod V F e S hS]
  apply prod_congr_one
  intro j hj
  split_ifs
  · exact inverse_congr_one _ (determinantFactor_constantCoeff (V j) (F j) he)
      (determinantFactor_congr_one (V j) (F j) he)
  · exact determinantFactor_congr_one (V j) (F j) he

private theorem coeff_prod_eq_small {R : Type v} [Field R] {I : Type w}
    (f : I → PowerSeries R) (d : I → ℕ) (n : ℕ) (s t : Finset I)
    (hst : t ⊆ s) (ht : ∀ i ∈ s, i ∉ t → n < d i)
    (hf : ∀ i, (PowerSeries.X : PowerSeries R) ^ d i ∣ f i - 1) :
    PowerSeries.coeff n (∏ i ∈ s, f i) = PowerSeries.coeff n (∏ i ∈ t, f i) := by
  classical
  let g : I → PowerSeries R := fun i ↦ if i ∈ t then f i else 1
  have hg : (∏ i ∈ s, g i) = ∏ i ∈ t, f i := by
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hst]
  rw [← hg]
  apply coeff_eq_of_congr_mod (prod_congr_mod s f g (n + 1) ?_) (by omega)
  intro i hi
  dsimp [g]
  split_ifs with hit
  · simp
  · exact dvd_trans (pow_dvd_pow _ (ht i hi hit)) (hf i)

/-- A finitely supported inverse alternating product is the inverse of the
source library's finite alternating characteristic-polynomial product.
Source: determinant convention in Euler-product proof Step 0. Zero modules
contribute one; the two parity choices cancel factor by factor.
(blueprint: lem-condensed-weil-euler-formal-algebra). -/
theorem inverseAlternating_as_inv {R : Type v} [Field R]
    (V : ℤ → ModuleCat.{u + 1} R) (F : ∀ j, End (V j))
    [∀ j, Module.Finite R (V j)] (e : ℕ) (he : e ≠ 0)
    (S : Finset ℤ) (hS : ∀ j, j ∉ S → IsZero (V j)) :
    inverseAlternating V F e =
      (LinearMap.alternatingCharpolyRevProd S (fun j ↦ (F j).hom) e)⁻¹ := by
  classical
  rw [inverseAlternating_eq_prod V F e S hS]
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by
    rw [LinearMap.constantCoeff_alternatingCharpolyRevProd S _ he]
    exact one_ne_zero)).mpr
  rw [LinearMap.alternatingCharpolyRevProd, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro j hj
  have hc := determinantFactor_constantCoeff (V j) (F j) (Nat.pos_of_ne_zero he)
  simp only [determinantFactor, dif_pos (inferInstance : Module.Finite R (V j))] at hc ⊢
  split_ifs
  · exact PowerSeries.inv_mul_cancel _ (by rw [hc]; exact one_ne_zero)
  · exact PowerSeries.mul_inv_cancel _ (by rw [hc]; exact one_ne_zero)

/-- Local factors and partial products stabilize in every coefficient. This is the
formal local-finiteness argument, independent of the trace formula.
Source: Euler-product proof, Step 2. Each determinant is one modulo T^degree by its
constant coefficient and polynomial substitution. Products and inverses preserve this
congruence. Bounded-degree closed points are finite by PointCount. Delete the remaining
factors modulo T^(n+1), and take coefficients; the same argument gives constant term one.
(blueprint: lem-condensed-weil-euler-formal-algebra). -/
theorem localEulerProduct_properties
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (c : WeilCoefficient ell) (K : strictWeilComplexCategory D ell hEll X₀ c)
    (iota : ∀ x : ClosedPoint D X₀, X₀.left.residueField x.val →+* D.k)
    (hiota : ∀ x, (iota x).comp (X₀.hom.residueFieldAlgebraMap x.val) =
      algebraMap D.k₀ D.k)
    (S : Finset ℤ) (hS : ∀ x j, j ∉ S →
      IsZero (localCohomology D ell hEll X₀ c K x (iota x) (hiota x) j)) :
    let A := localFactor D ell hEll X₀ c K iota hiota
    let L := lFunction D ell hEll X₀ c K iota hiota
    (∀ n : ℕ, Set.Finite {x : ClosedPoint D X₀ | localClosedPointDegree D X₀ x ≤ n}) ∧
    (∀ n : ℕ, Set.Finite {x : ClosedPoint D X₀ |
      ∃ m ≤ n, PowerSeries.coeff m (A x) ≠ PowerSeries.coeff m (1 : PowerSeries _)}) ∧
    PowerSeries.constantCoeff L = 1 ∧
    (∀ (n : ℕ) (s : Finset (ClosedPoint D X₀)),
      (∀ x, localClosedPointDegree D X₀ x ≤ n → x ∈ s) →
      PowerSeries.coeff n L = PowerSeries.coeff n (∏ x ∈ s, A x)) := by
  classical
  dsimp only
  let A := localFactor D ell hEll X₀ c K iota hiota
  have hf : ∀ x, (PowerSeries.X : PowerSeries (Scalar c)) ^
      localClosedPointDegree D X₀ x ∣ A x - 1 := by
    intro x
    exact inverseAlternating_congr_one _ _ (degree_pos D X₀ x) S (hS x)
  have hc : ∀ x, PowerSeries.constantCoeff (A x) = 1 := by
    intro x
    exact inverseAlternating_constantCoeff _ _ (degree_pos D X₀ x) S (hS x)
  have hp (n : ℕ) :
      (∏ᶠ x : {x : ClosedPoint D X₀ // localClosedPointDegree D X₀ x ≤ n}, A x.val) =
        ∏ x ∈ (finiteDegree D X₀ n).toFinset, A x := by
    let : Fintype {x : ClosedPoint D X₀ // localClosedPointDegree D X₀ x ≤ n} :=
      (finiteDegree D X₀ n).fintype
    rw [finprod_eq_prod_of_fintype]
    exact (Finset.prod_subtype _ (by simp) A).symm
  refine ⟨finiteDegree D X₀, ?_, ?_, ?_⟩
  · intro n
    apply (finiteDegree D X₀ n).subset
    rintro x ⟨m, hm, hne⟩
    by_contra hxn
    change ¬localClosedPointDegree D X₀ x ≤ n at hxn
    exact hne (coeff_eq_of_congr_mod (hf x) (by omega))
  · change PowerSeries.coeff 0
      (∏ᶠ x : {x : ClosedPoint D X₀ // localClosedPointDegree D X₀ x ≤ 0}, A x.val) = 1
    rw [hp]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_prod]
    exact Finset.prod_eq_one (fun x _ ↦ hc x)
  · intro n s hs
    simp only [lFunction, PowerSeries.coeff_mk]
    change PowerSeries.coeff n
      (∏ᶠ x : {x : ClosedPoint D X₀ // localClosedPointDegree D X₀ x ≤ n}, A x.val) = _
    rw [hp]
    symm
    apply coeff_prod_eq_small A (localClosedPointDegree D X₀) n s
      (finiteDegree D X₀ n).toFinset
    · intro x hx
      exact hs x (by simpa using hx)
    · intro x _ hx
      have : ¬localClosedPointDegree D X₀ x ≤ n := by simpa using hx
      omega
    · exact hf

/-- Finite support makes the global determinant a finite product; on a curve its
three surviving factors give the quotient. A coefficient embedding preserves that
finite product and the inverses of its constant-one determinants.
Source: Euler-product proof, Steps 5 and 6. Zero modules have determinant one.
Reduce finprod to any finite set containing its support, expand {0,1,2}, and commute
coefficient mapping with finite multiplication and with inversion of units.
(blueprint: lem-condensed-weil-euler-formal-algebra). -/
theorem globalEulerProduct_properties {R : Type v} [Field R]
    (V : ℤ → ModuleCat.{u + 1} R) (F : ∀ j, End (V j))
    (S : Finset ℤ) (hS : ∀ j, j ∉ S → IsZero (V j)) :
    (∀ T : Finset ℤ, (∀ j, j ∉ T → IsZero (V j)) →
      inverseAlternating V F 1 =
        ∏ j ∈ T, if Even j then (determinantFactor (V j) (F j) 1)⁻¹
          else determinantFactor (V j) (F j) 1) ∧
    ((∀ j : ℤ, j ∉ ({0, 1, 2} : Finset ℤ) → IsZero (V j)) →
      inverseAlternating V F 1 = determinantFactor (V 1) (F 1) 1 *
        (determinantFactor (V 0) (F 0) 1 * determinantFactor (V 2) (F 2) 1)⁻¹) ∧
    (∀ (E : Type w) [Field E] (f : R →+* E),
      PowerSeries.map f (inverseAlternating V F 1) =
        ∏ᶠ j : ℤ, if Even j then
          (PowerSeries.map f (determinantFactor (V j) (F j) 1))⁻¹
          else PowerSeries.map f (determinantFactor (V j) (F j) 1)) := by
  classical
  refine ⟨fun T hT ↦ inverseAlternating_eq_prod V F 1 T hT, ?_, ?_⟩
  · intro h
    rw [inverseAlternating_eq_prod V F 1 {0, 1, 2} h]
    norm_num [Finset.prod_insert, PowerSeries.mul_inv_rev]
    ring
  · intro E _ f
    rw [inverseAlternating_eq_prod V F 1 S hS, map_prod]
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
    · apply Finset.prod_congr rfl
      intro j hj
      split_ifs
      · exact map_inverse f _ (determinantFactor_constantCoeff (V j) (F j) (by decide))
      · rfl
    · intro j hj
      by_contra hjS
      have hj1 := determinantFactor_of_isZero (V j) (F j) 1 (hS j hjS)
      simp [Function.mem_mulSupport, hj1] at hj

end WeilConjectures.CondensedWeilEuler
