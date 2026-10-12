/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.DeligneLaumon.AffineLine.Endpoints
public import WeilConjectures.WeilSheaf.LFunction
public import WeilConjectures.WeilSheaf.LowerStarId
public import WeilConjectures.WeilSheaf.TateTwistCohomology

/-!
# Compactly supported cohomology of a lisse Weil sheaf on an affine curve

On a smooth geometrically connected affine curve `U₀` over a finite field, a lisse Weil sheaf
has no compactly supported cohomology in degree zero: a compactly supported global section of a
lisse sheaf is locally constant, so its support is open and closed, hence empty or all of the
connected curve `U`, which is not proper.

## Main statements

- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_zero`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `lem-a1-affine-hc0`: Vanishing of `H_c⁰` on a nonproper curve.

Let `U₀` be a smooth geometrically connected affine curve and `ℱ` a lisse Weil sheaf on `U₀`.
Then `H_c⁰ (U, ℱ) = 0`.

A class in `H_c⁰` is a global section of `ℱ` whose support is proper over the base field. By
lissity a global section of `ℱ` is locally constant, so on the connected curve `U` it vanishes
as soon as it vanishes at one geometric point; the support of a nonzero section is therefore
all of `U`, which is not proper. Here it is the case `j = 𝟙` of
`AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage_zero`. -/
theorem subsingleton_compactlySupportedCohomology_zero [IsAffine U]
    [SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l U)
    (hF : F.IsLisse) :
    Subsingleton (F.compactlySupportedCohomology 0).carrier :=
  have := subsingleton_compactlySupportedCohomology_directImage_zero (𝟙 U) F hF
  (compactlySupportedCohomologyEquivOfIso ((lowerStarIdIso k₀ l U).app F).symm 0)
    |>.toLinearEquiv.toEquiv.subsingleton


/-- Blueprint `lem-a1-affine-hc2`: Description of `H_c²` on an affine curve.

Let `U₀` be a smooth geometrically connected affine curve and `ℱ` a lisse Weil sheaf on `U₀`,
with local generic fibre `V`. Then `H_c² (U, ℱ) ≅ V_{π₁(U)} (-1)` Frobenius-equivariantly, where
the geometric coinvariants `V_{π₁(U)}` are `Γ(U, ℱ^∨)^∨`
(`AlgebraicGeometry.WeilSheaf.geometricCoinvariants`) and `(-1)` multiplies the Frobenius by
`q`. This follows from global Verdier duality on a smooth compactification and the description
of global sections as invariants. -/
theorem nonempty_equiv_compactlySupportedCohomology_two [IsAffine U]
    [SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l U)
    (hF : F.IsLisse) :
    Nonempty ((F.compactlySupportedCohomology 2).Equiv
      ((F.geometricCoinvariants hF).tateTwist (Nat.card k₀) (-1))) := by
  obtain ⟨e⟩ := nonempty_equiv_compactlySupportedCohomology_directImage_two (𝟙 U) F hF
  exact ⟨(compactlySupportedCohomologyEquivOfIso ((lowerStarIdIso k₀ l U).app F).symm 2).trans
    e⟩

/-- The compactly supported cohomology of a lisse Weil sheaf on a smooth geometrically
connected affine curve vanishes outside degrees `1` and `2`. -/
theorem subsingleton_compactlySupportedCohomology_of_notMem [IsAffine U]
    [SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l U)
    (hF : F.IsLisse) {i : ℤ} (hi : i ∉ ({1, 2} : Finset ℤ)) :
    Subsingleton (F.compactlySupportedCohomology i).carrier := by
  rw [Finset.mem_insert, Finset.mem_singleton] at hi
  obtain rfl | hi' : i = 0 ∨ i < 0 ∨ 2 < i := by omega
  · exact subsingleton_compactlySupportedCohomology_zero F hF
  · exact subsingleton_compactlySupportedCohomology_of_isAffine F hi'

open PowerSeries in
/-- Blueprint `cor-rp-euler-product`: Euler product of the `L`-function of a lisse sheaf.

Let `U₀` be a smooth geometrically connected affine curve and `ℱ` a lisse Weil sheaf on `U₀`.
Then, as power series in `T`,

`∏_{x ∈ |U₀|} det (1 - F_x T ^ {e_x} ∣ ℱ_x̄)⁻¹ = det (1 - F T ∣ H_c¹) / det (1 - F T ∣ H_c²)`,

the product over the closed points being locally finite: for every `n`, the coefficient of
`T ^ n` of the finite product over any finite set `s` of closed points containing those of
degree at most `n` is the coefficient of `T ^ n` of the right-hand side. This is the
Euler-product form of the trace formula (`thm-trf-l-function-euler-product`) for `ℱ` placed in
degree zero, whose compactly supported cohomology is concentrated in degrees `0, 1, 2`, together
with `H_c⁰ (U, ℱ) = 0` (`lem-a1-affine-hc0`). -/
theorem coeff_prod_inv_localPolynomial_stalk_eq [IsAffine U]
    [SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l U)
    (hF : F.IsLisse) (n : ℕ) (s : Finset U.finitePoints)
    (hs : ∀ x : U.finitePoints, (U ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ≤ n → x ∈ s) :
    coeff n (∏ x ∈ s, (((F.stalk x).localPolynomial.comp
        (Polynomial.X ^ (U ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) : Polynomial _) :
          (PadicAlgCl l)⟦X⟧)⁻¹) =
      coeff n (((F.compactlySupportedCohomology 1).localPolynomial : (PadicAlgCl l)⟦X⟧) *
        ((F.compactlySupportedCohomology 2).localPolynomial : (PadicAlgCl l)⟦X⟧)⁻¹) := by
  rw [coeff_prod_inv_localPolynomial_stalk F
    (fun i hi ↦ subsingleton_compactlySupportedCohomology_of_notMem F hF hi) n s hs,
    LinearMap.alternatingCharpolyRevProd, Finset.prod_pair (by decide), if_neg (by decide),
    if_pos (by decide), pow_one, Polynomial.comp_X, Polynomial.comp_X]
  congr 1
  simp only [FrobeniusModule.localPolynomial]
  have h₁ : constantCoeff
      ((F.compactlySupportedCohomology 1).frobeniusEnd.charpolyRev : (PadicAlgCl l)⟦X⟧) ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      LinearMap.coeff_zero_charpolyRev]
    exact one_ne_zero
  have h₂ : constantCoeff
      ((F.compactlySupportedCohomology 2).frobeniusEnd.charpolyRev : (PadicAlgCl l)⟦X⟧) ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      LinearMap.coeff_zero_charpolyRev]
    exact one_ne_zero
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp), mul_mul_mul_comm,
    PowerSeries.mul_inv_cancel _ h₁, PowerSeries.inv_mul_cancel _ h₂, one_mul]

end WeilSheaf

end AlgebraicGeometry
