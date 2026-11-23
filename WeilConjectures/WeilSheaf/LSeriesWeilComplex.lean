/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LFunction
public import WeilConjectures.WeilSheaf.StalkIso

/-!
# The `L`-function of a Weil complex

Let `X₀` be a separated scheme of finite type over the finite field `k₀ = 𝔽_q` and `K` a Weil
complex on `X₀` with coefficients in `ℚ̄_ℓ`. For a closed point `x` of degree `e_x`, with local
Frobenius `F_x` on the stalks `𝓗ʲ(K)_x̄`, the local factor of the `L`-function of `K` at `x` is

`det (1 - T ^ {e_x} F_x ∣ K_x̄)⁻¹ = ∏_j det (1 - T ^ {e_x} F_x ∣ 𝓗ʲ(K)_x̄) ^ (-(-1) ^ j)`,

and the `L`-function `L(X₀, K, T)` is the product of the local factors over all closed points.
The product converges `T`-adically, and by the Grothendieck–Lefschetz trace formula

`L(X₀, K, T) = ∏_i det (1 - T F ∣ H_cⁱ(X, K)) ^ ((-1) ^ (i + 1))`.

In particular `L(X₀, K, T)` is the expansion of a rational function with value `1` at `0`, and
for proper `X₀` compactly supported cohomology may be replaced by ordinary cohomology.

The `L`-series of a Weil sheaf transported to `ℂ` along an embedding `ι : ℚ̄_ℓ → ℂ` is
`AlgebraicGeometry.WeilSheaf.lSeries`.

## Main definitions

- `AlgebraicGeometry.WeilComplex.lFactor`: the local factor `det (1 - T ^ {e_x} F_x ∣ K_x̄)⁻¹`.
- `AlgebraicGeometry.WeilComplex.lSeries`: the `L`-function `L(X₀, K, T)`, the product of the
  local factors.

## Main statements

- `AlgebraicGeometry.WeilComplex.finite_setOf_not_X_pow_dvd_lFactor_sub_one`: modulo `T ^ n`
  only finitely many local factors differ from `1`.
- `AlgebraicGeometry.WeilComplex.hasProd_lFactor`: the product of the local factors converges
  to `L(X₀, K, T)`.
- `AlgebraicGeometry.WeilComplex.lSeries_eq_inv_alternatingCharpolyRevProd`: the cohomological
  expression of `L(X₀, K, T)`.
- `AlgebraicGeometry.WeilComplex.exists_lSeries_mul_eq`: `L(X₀, K, T)` is rational.
- `AlgebraicGeometry.WeilComplex.lSeries_eq_inv_alternatingCharpolyRevProd_cohomology`: the
  cohomological expression for proper `X₀` in terms of ordinary cohomology.

## Implementation details

The products over the degrees `j` of the stalk cohomology run over a finite set of degrees
outside of which the cohomology sheaves `𝓗ʲ(K)` vanish; the local factor is defined with one
such set, chosen once, and does not depend on the choice
(`AlgebraicGeometry.WeilComplex.lFactor_eq`). The infinite product is taken for the product
topology on `ℚ̄_ℓ⟦T⟧`: it is locally finite coefficientwise, which is `T`-adic convergence.
-/

@[expose] public section

universe u

open CategoryTheory Limits PowerSeries

open scoped PowerSeries.WithPiTopology

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilComplex

variable (K : WeilComplex k₀ l X)

/-- The local factor `det (1 - T ^ {e_x} F_x ∣ K_x̄)⁻¹` of the `L`-function of a Weil complex `K`
at a closed point `x` of degree `e_x`: the inverse of the alternating determinant
`∏_j det (1 - T ^ {e_x} F_x ∣ 𝓗ʲ(K)_x̄) ^ ((-1) ^ j)` of the local Frobenius `F_x` on the stalks
of the cohomology sheaves. -/
noncomputable def lFactor (x : X.finitePoints) : (PadicAlgCl l)⟦X⟧ :=
  (LinearMap.alternatingCharpolyRevProd K.exists_finset_isZero_homologySheaf.choose
    (fun j ↦ (K.stalk j x).frobeniusEnd) ((X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1))⁻¹

/-- The local factor at `x` is the inverse of the alternating determinant over any finite set
of degrees outside of which the cohomology sheaves vanish. -/
theorem lFactor_eq {T : Finset ℤ} (hT : ∀ j ∉ T, IsZero ((homologySheaf j).obj K))
    (x : X.finitePoints) :
    K.lFactor x = (LinearMap.alternatingCharpolyRevProd T (fun j ↦ (K.stalk j x).frobeniusEnd)
      ((X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1))⁻¹ := by
  classical
  have hT₀ := K.exists_finset_isZero_homologySheaf.choose_spec
  have h (T' : Finset ℤ) (hT' : ∀ j ∉ T', IsZero ((homologySheaf j).obj K))
      (hsub : T' ⊆ K.exists_finset_isZero_homologySheaf.choose ∪ T) :
      LinearMap.alternatingCharpolyRevProd T' (fun j ↦ (K.stalk j x).frobeniusEnd)
          ((X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) =
        LinearMap.alternatingCharpolyRevProd (K.exists_finset_isZero_homologySheaf.choose ∪ T)
          (fun j ↦ (K.stalk j x).frobeniusEnd)
          ((X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) :=
    LinearMap.alternatingCharpolyRevProd_eq_of_subset hsub _
      (fun j _ hj ↦ WeilSheaf.subsingleton_stalk_of_isZero (hT' j hj) x) _
  rw [lFactor, h _ hT₀ Finset.subset_union_left, h _ hT Finset.subset_union_right]

/-- The local factor at a closed point `x` of degree `e_x` is congruent to `1` modulo
`T ^ {e_x}`. -/
theorem X_pow_dvd_lFactor_sub_one (x : X.finitePoints) :
    PowerSeries.X ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ∣ K.lFactor x - 1 :=
  LinearMap.X_pow_dvd_inv_alternatingCharpolyRevProd_sub_one _ _
    ((X ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2)

/-- The `L`-function `L(X₀, K, T) = ∏_x det (1 - T ^ {e_x} F_x ∣ K_x̄)⁻¹` of a Weil complex `K`:
the product of the local factors over all closed points `x` of `X₀`. -/
noncomputable def lSeries : (PadicAlgCl l)⟦X⟧ :=
  ∏' x : X.finitePoints, K.lFactor x

variable [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- For every `n`, only finitely many local factors of the `L`-function of `K` differ from `1`
modulo `T ^ n`. -/
theorem finite_setOf_not_X_pow_dvd_lFactor_sub_one (n : ℕ) :
    {x : X.finitePoints | ¬ PowerSeries.X ^ n ∣ K.lFactor x - 1}.Finite :=
  ((X ↘ Spec (CommRingCat.of k₀)).finite_setOf_degreeOver_le n).subset fun x hx ↦ by
    by_contra h
    exact hx ((pow_dvd_pow PowerSeries.X (not_le.1 h).le).trans
      (K.X_pow_dvd_lFactor_sub_one x))

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- The product of the local factors `det (1 - T ^ {e_x} F_x ∣ K_x̄)⁻¹` over the closed points
converges to `∏_i det (1 - T F ∣ H_cⁱ(X, K)) ^ ((-1) ^ (i + 1))`, for a finite set `S` of degrees
outside of which `H_cⁱ(X, K)` vanishes. -/
theorem hasProd_lFactor_inv_alternatingCharpolyRevProd {S : Finset ℤ}
    (hS : ∀ i ∉ S, Subsingleton (K.compactlySupportedCohomology i).carrier) :
    HasProd K.lFactor (LinearMap.alternatingCharpolyRevProd S
      (fun i ↦ (K.compactlySupportedCohomology i).frobeniusEnd) 1)⁻¹ := by
  classical
  set f := X ↘ Spec (CommRingCat.of k₀)
  have hfin := f.finite_setOf_degreeOver_le
  set s : ℕ → Finset X.finitePoints := fun n ↦ (hfin n).toFinset
  have hs {n : ℕ} {x : X.finitePoints} (hx : f.degreeOver x.1 ≤ n) : x ∈ s n :=
    (hfin n).mem_toFinset.2 hx
  have h := WithPiTopology.hasProd_of_X_pow_dvd_sub_one s fun n x hx ↦
    (pow_dvd_pow PowerSeries.X (not_le.1 fun h ↦ hx (hs h))).trans
      (K.X_pow_dvd_lFactor_sub_one x)
  convert h using 1
  ext n
  obtain ⟨T, hT⟩ := K.exists_finset_isZero_homologySheaf
  rw [coeff_mk, Finset.prod_congr rfl fun x _ ↦ K.lFactor_eq hT x]
  exact (K.coeff_prod_inv_alternatingCharpolyRevProd_stalk hS hT n (s n) fun x hx ↦ hs hx).symm

/-- The `L`-function of a Weil complex is given by the cohomological product
`L(X₀, K, T) = ∏_i det (1 - T F ∣ H_cⁱ(X, K)) ^ ((-1) ^ (i + 1))`, for a finite set `S` of
degrees outside of which `H_cⁱ(X, K)` vanishes. -/
theorem lSeries_eq_inv_alternatingCharpolyRevProd {S : Finset ℤ}
    (hS : ∀ i ∉ S, Subsingleton (K.compactlySupportedCohomology i).carrier) :
    K.lSeries = (LinearMap.alternatingCharpolyRevProd S
      (fun i ↦ (K.compactlySupportedCohomology i).frobeniusEnd) 1)⁻¹ :=
  (K.hasProd_lFactor_inv_alternatingCharpolyRevProd hS).tprod_eq

/-- The product of the local factors `det (1 - T ^ {e_x} F_x ∣ K_x̄)⁻¹` over the closed points
converges `T`-adically to the `L`-function `L(X₀, K, T)`. -/
theorem hasProd_lFactor : HasProd K.lFactor K.lSeries := by
  obtain ⟨S, hS⟩ := K.exists_finset_subsingleton_compactlySupportedCohomology
  rw [K.lSeries_eq_inv_alternatingCharpolyRevProd hS]
  exact K.hasProd_lFactor_inv_alternatingCharpolyRevProd hS

/-- The `L`-function of a Weil complex has constant coefficient `1`. -/
theorem constantCoeff_lSeries : constantCoeff K.lSeries = 1 := by
  obtain ⟨S, hS⟩ := K.exists_finset_subsingleton_compactlySupportedCohomology
  rw [K.lSeries_eq_inv_alternatingCharpolyRevProd hS, constantCoeff_inv,
    LinearMap.constantCoeff_alternatingCharpolyRevProd _ _ one_ne_zero, inv_one]

/-- The `L`-function of a Weil complex is the expansion at `0` of a rational function with
value `1` at `0`: `L(X₀, K, T) Q = P` for polynomials `P` and `Q` with constant term `1`. -/
theorem exists_lSeries_mul_eq :
    ∃ P Q : Polynomial (PadicAlgCl l), P.coeff 0 = 1 ∧ Q.coeff 0 = 1 ∧
      K.lSeries * (Q : (PadicAlgCl l)⟦X⟧) = P := by
  classical
  obtain ⟨S, hS⟩ := K.exists_finset_subsingleton_compactlySupportedCohomology
  set a : ℤ → Polynomial (PadicAlgCl l) :=
    fun i ↦ (K.compactlySupportedCohomology i).frobeniusEnd.charpolyRev
  have ha (i : ℤ) : (a i).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, LinearMap.eval_charpolyRev]
  have ha' (i : ℤ) :
      constantCoeff ((a i : Polynomial (PadicAlgCl l)) : (PadicAlgCl l)⟦X⟧) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, ha]
    exact one_ne_zero
  have hcoeff (p : ℤ → Prop) [DecidablePred p] :
      (∏ i ∈ S with p i, a i).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
    exact Finset.prod_eq_one fun i _ ↦ by rw [← Polynomial.coeff_zero_eq_eval_zero, ha]
  refine ⟨∏ i ∈ S with ¬ Even i, a i, ∏ i ∈ S with Even i, a i, hcoeff _, hcoeff _, ?_⟩
  set Δ := LinearMap.alternatingCharpolyRevProd S
    (fun i ↦ (K.compactlySupportedCohomology i).frobeniusEnd) 1
  have hΔ : constantCoeff Δ ≠ 0 := by
    rw [LinearMap.constantCoeff_alternatingCharpolyRevProd _ _ one_ne_zero]
    exact one_ne_zero
  have key : Δ * ((∏ i ∈ S with ¬ Even i, a i : Polynomial (PadicAlgCl l)) :
      (PadicAlgCl l)⟦X⟧) = ((∏ i ∈ S with Even i, a i : Polynomial (PadicAlgCl l)) :
      (PadicAlgCl l)⟦X⟧) := by
    have hc (p : ℤ → Prop) [DecidablePred p] :
        ((∏ i ∈ S with p i, a i : Polynomial (PadicAlgCl l)) : (PadicAlgCl l)⟦X⟧) =
          ∏ i ∈ S with p i, ((a i : Polynomial (PadicAlgCl l)) : (PadicAlgCl l)⟦X⟧) :=
      map_prod Polynomial.coeToPowerSeries.ringHom _ _
    rw [hc, hc]
    simp only [Finset.prod_filter, Δ, LinearMap.alternatingCharpolyRevProd, pow_one,
      Polynomial.comp_X]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    split_ifs
    · rw [mul_one]
    · exact PowerSeries.inv_mul_cancel _ (ha' i)
  rw [K.lSeries_eq_inv_alternatingCharpolyRevProd hS, ← key, ← mul_assoc,
    PowerSeries.inv_mul_cancel _ hΔ, one_mul]

end WeilComplex

section Proper

variable [IsProper (X ↘ Spec (CommRingCat.of k₀))]

/-- For proper `X₀`, the `L`-function of a Weil complex is given by the cohomological product
`L(X₀, K, T) = ∏_i det (1 - T F ∣ Hⁱ(X, K)) ^ ((-1) ^ (i + 1))` over ordinary cohomology, for a
finite set `S` of degrees outside of which `Hⁱ(X, K)` vanishes. -/
theorem WeilComplex.lSeries_eq_inv_alternatingCharpolyRevProd_cohomology
    (K : WeilComplex k₀ l X) {S : Finset ℤ}
    (hS : ∀ i ∉ S, Subsingleton (K.cohomology i).carrier) :
    K.lSeries = (LinearMap.alternatingCharpolyRevProd S
      (fun i ↦ (K.cohomology i).frobeniusEnd) 1)⁻¹ := by
  have e (i : ℤ) := (K.nonempty_equiv_compactlySupportedCohomology_cohomology i).some
  rw [K.lSeries_eq_inv_alternatingCharpolyRevProd (S := S) fun i hi ↦
    have := hS i hi
    (e i).toLinearEquiv.toEquiv.subsingleton]
  refine congrArg Inv.inv (Finset.prod_congr rfl fun i _ ↦ ?_)
  rw [LinearMap.charpolyRev_def, LinearMap.charpolyRev_def, (e i).charpoly_frobeniusEnd]

end Proper

end AlgebraicGeometry
