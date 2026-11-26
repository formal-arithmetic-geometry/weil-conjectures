/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Artinian.Defs
import WeilConjectures.RingTheory.PopescuParameterCoefficientModel

/-!
# Coefficient construction for compatible Popescu parameters

We construct the parameters `u_i` and their coefficient equations
`u_i^(2N) = ∑_j μ_ij f(a_j)` in the coefficient model `D'[t]`, independently of any presented
standardizer algebra.

## References

* [Stacks, Tag 07FJ] (proof)
-/

@[expose] public section

set_option autoImplicit false

universe u v w
namespace Algebra

/-- Construct the parameters and their coefficient equations, independently of any presented
standardizer algebra. -/
theorem exists_popescu_parameter_coefficients
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (hreg : IsGeometricallyRegular k Λ)
    (N : ℕ) (hN : 0 < N)
    (hpower : IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ N ≤
      (Ideal.map α.toRingHom (singularIdeal k A)).map
        (algebraMap Λ (Localization.AtPrime q.asIdeal)))
    (d : ℕ) (hd : d =
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).spanFinrank)
    (s : ℕ) (a : Fin s → A) (ha : Ideal.span (Set.range a) = singularIdeal k A)
    (c : ℕ) (hc : 0 < c) :
    let S := MvPolynomial (Fin d) k
    ∃ (m : ℕ) (_ : Algebra (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k (MvPolynomial (Fin m) k) Λ)
      (_ : Algebra S (MvPolynomial (Fin m) k))
      (_ : IsScalarTower k S (MvPolynomial (Fin m) k))
      (_ : Algebra S Λ) (_ : IsScalarTower S (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k S Λ)
      (ell : Fin d × Fin s → Λ) (π : Fin (d + 1) → MvPolynomial (Fin m) k),
      (∀ i, algebraMap S Λ (MvPolynomial.X i) ^ (2 * N) =
        ∑ j : Fin s, ell (i, j) * α (a j)) ∧
      (∀ i, π i = 0 ∨ ∃ j : Fin d,
        π i = algebraMap S (MvPolynomial (Fin m) k) (MvPolynomial.X j ^ c)) ∧
      (∀ i, algebraMap (MvPolynomial (Fin m) k) Λ (π i) ∈ q.asIdeal) ∧
      (∀ (i : Fin (d + 1))
        (x : MvPolynomial (Fin m) k ⧸ Ideal.span
          {y | ∃ j : Fin (d + 1), j.val < i.val ∧ y = π j ^ 8}),
        π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
      (∀ (i : Fin (d + 1))
        (x : Λ ⧸ Ideal.span
          {y | ∃ j : Fin (d + 1), j.val < i.val ∧
            y = algebraMap (MvPolynomial (Fin m) k) Λ (π j) ^ 8}),
        π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
    let R := MvPolynomial (Fin m) k
    let J := Ideal.span (Set.range (fun i : Fin (d + 1) ↦ π i ^ 8))
    let Q := Localization.AtPrime (q.asIdeal.under R)
    let L := Localization.AtPrime q.asIdeal
    letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
    let JQ := J.map (algebraMap R Q)
    let JL := (J.map (algebraMap R Λ)).map (algebraMap Λ L)
    ∃ (n : ℕ), 0 < n ∧ IsLocalRing.maximalIdeal L ^ n ≤ JL ∧
      ∃ (I₀ : Ideal R) (K : Ideal L),
        I₀.map (algebraMap R Q) ≤ JQ ∧ K ≤ JL ∧
        (I₀.map (algebraMap R Q)).map (algebraMap Q L) ≤ K ∧
        ∃ (t : ℕ) (D' : Type (max u v)) (_ : CommRing D')
          (_ : IsLocalRing D') (_ : IsArtinianRing D'),
          let E := MvPolynomial (Fin t) D'
          ∃ (_ : Algebra R E) (_ : Algebra (R ⧸ I₀) E)
            (_ : IsScalarTower R (R ⧸ I₀) E)
            (_ : Algebra S E) (_ : IsScalarTower S R E)
            (_ : Algebra k E) (_ : IsScalarTower k S E),
            EssentiallySmooth (R ⧸ I₀) E ∧
            ∃ (f : A →ₐ[k] E) (μ : Fin d × Fin s → E)
              (b : E →ₐ[R] L ⧸ K),
              (∀ i, algebraMap S E (MvPolynomial.X i) ^ (2 * N) =
                ∑ j : Fin s, μ (i, j) * f (a j)) ∧
              (∀ x, b (f x) = Ideal.Quotient.mk K (algebraMap Λ L (α x))) ∧
              (∀ ij, b (μ ij) = Ideal.Quotient.mk K (algebraMap Λ L (ell ij))) := by
  classical
  obtain ⟨m, algR, towerkR, algSR, towerkSR, algSL, towerSRL, towerkSL,
    ell, π, heq, hπ, hq, hkerR, hkerL, n, hn, hbound, I₀, K,
    hI₀, hK, hIK, D', ringD, localD, artD, algkD, algRE, algQE,
    towerRQE, algSE, towerSRE, algkE, towerkSE, hsmooth,
    towerkDE, f₀, b, u₀, δ, coeff, hinj, hX, hδ, hf₀, hcoeff⟩ :=
    exists_popescu_parameter_coefficient_model p hp α q hreg N hN hpower d hd s a ha c hc
  let R := MvPolynomial (Fin m) k
  let S := MvPolynomial (Fin d) k
  let L := Localization.AtPrime q.asIdeal
  let E := MvPolynomial (Fin d) D'
  let : CommRing D' := ringD
  let : IsLocalRing D' := localD
  let : IsArtinianRing D' := artD
  let : Algebra k R := inferInstance
  let : Algebra R Λ := algR
  let : IsScalarTower k R Λ := towerkR
  let : Algebra S R := algSR
  let : IsScalarTower k S R := towerkSR
  let : Algebra S Λ := algSL
  let : IsScalarTower S R Λ := towerSRL
  let : IsScalarTower k S Λ := towerkSL
  let : Algebra k D' := algkD
  let : Algebra R E := algRE
  let : Algebra (R ⧸ I₀) E := algQE
  let : IsScalarTower R (R ⧸ I₀) E := towerRQE
  let : Algebra S E := algSE
  let : IsScalarTower S R E := towerSRE
  let : Algebra k E := algkE
  let : IsScalarTower k S E := towerkSE
  let : IsScalarTower k D' E := towerkDE
  let f : A →ₐ[k] E := (IsScalarTower.toAlgHom k D' E).comp f₀
  let μ : Fin d × Fin s → E := fun ij ↦
    MvPolynomial.C (coeff ij * (↑((δ ij.1)⁻¹) : D') ^ (2 * N)) *
      MvPolynomial.X ij.1 ^ (2 * N)
  have hf (x : A) : f x = MvPolynomial.C (f₀ x) := rfl
  have hbX (i : Fin d) : b (algebraMap S E (MvPolynomial.X i)) =
      Ideal.Quotient.mk K (algebraMap Λ L (algebraMap S Λ (MvPolynomial.X i))) := by
    let Q := Localization.AtPrime (q.asIdeal.under R)
    let := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
    rw [IsScalarTower.algebraMap_apply S R E, b.commutes]
    rw [IsScalarTower.algebraMap_apply S R Λ]
    rfl
  let g : D' →+* L ⧸ K := b.toRingHom.comp MvPolynomial.C
  have hconst (i : Fin d) : u₀ i ^ (2 * N) =
      ∑ j : Fin s, coeff (i, j) * (↑((δ i)⁻¹) : D') ^ (2 * N) * f₀ (a j) := by
    have hrel : (u₀ i * (↑(δ i) : D')) ^ (2 * N) =
        ∑ j : Fin s, coeff (i, j) * f₀ (a j) := by
      apply hinj
      change g _ = g _
      simp only [map_pow, map_mul, map_sum]
      change (b (MvPolynomial.C (u₀ i)) * b (MvPolynomial.C (↑(δ i) : D'))) ^
        (2 * N) = ∑ j : Fin s, b (MvPolynomial.C (coeff (i, j))) *
          b (MvPolynomial.C (f₀ (a j)))
      rw [← hδ i, ← map_mul, ← hX i, hbX i]
      simp only [hcoeff, hf₀]
      simpa only [map_pow, map_sum, map_mul] using
        congrArg (fun z : Λ ↦ Ideal.Quotient.mk K (algebraMap Λ L z)) (heq i)
    calc
      u₀ i ^ (2 * N) =
          (u₀ i * (↑(δ i) : D')) ^ (2 * N) *
            (↑((δ i)⁻¹) : D') ^ (2 * N) := by
        rw [← mul_pow, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by
        rw [hrel, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
  refine ⟨m, algR, towerkR, algSR, towerkSR, algSL, towerSRL, towerkSL,
    ell, π, heq, hπ, hq, hkerR, hkerL, n, hn, hbound, I₀, K,
    hI₀, hK, hIK, d, D', ringD, localD, artD, algRE, algQE,
    towerRQE, algSE, towerSRE, algkE, towerkSE, hsmooth, f, μ, b, ?_, ?_, ?_⟩
  · intro i
    rw [hX i, mul_pow, ← map_pow, hconst i]
    simp only [μ, map_sum, map_mul, map_pow]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [hf]
    ring
  · intro x
    rw [hf]
    exact hf₀ x
  · intro ij
    change b (MvPolynomial.C (coeff ij * (↑((δ ij.1)⁻¹) : D') ^ (2 * N)) *
      MvPolynomial.X ij.1 ^ (2 * N)) = _
    rw [map_mul, map_pow, hδ ij.1]
    change g (coeff ij * (↑((δ ij.1)⁻¹) : D') ^ (2 * N)) *
      g (↑(δ ij.1) : D') ^ (2 * N) = _
    rw [← map_pow, ← map_mul, mul_assoc, ← mul_pow, Units.inv_mul, one_pow, mul_one]
    exact hcoeff ij

end Algebra
