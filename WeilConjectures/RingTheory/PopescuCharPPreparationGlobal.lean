/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.RingTheory.StrictlyStandardElement
public import Mathlib.Algebra.MvPolynomial.Basic
public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Artinian.Defs

import WeilConjectures.RingTheory.PopescuUniversalStandardizer
import WeilConjectures.RingTheory.PopescuParameterSolution

/-!
# Global auxiliary factorization in characteristic p

The standardized algebra of the positive characteristic case of the local resolution step in
Popescu's theorem admits a factorization before localizing the polynomial base.

## Implementation details

The algebra `B = A[x_i, z_ij] / (x_i^(2N) - ∑_j z_ij a_j)` is smooth over `k[x]` on the `a_j`- and
`x_i`-opens and is improved to a retract `C_old` with `x_i^c` strictly standard; put `e = 8 c` and
`n = N + d e`. The solution modulo `m^n` (Tag 07FH) gives parameters `π_i`, rescaled by Ogoma's
lemma, and enlargements (Tag 07FI) give units `δ_i` and coefficients `λ_ij` with
`(δ_i π_i)^(2N) = ∑_j a_j λ_ij`. Base change along `x_i ↦ π_i t_i` gives `C`, and `E = D'[t]` gives
the factorization; this step does not yet localize `E`. The parameter list is padded by a zero,
and small representatives put `C` and `E` in `Type (max u v)`.

## References

* [Stacks, Tag 07FJ] (items on powers through the eighth resolution)
* [Stacks, Tag 07FH]
* [Stacks, Tag 07FI]
-/

@[expose] public section
universe u v w
open scoped TensorProduct
namespace Algebra

/-- The standardizer admits a factorization before localizing the polynomial base at `q`, at an
earlier thickening. -/
theorem exists_popescu_char_p_preparation_global
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (hreg : IsGeometricallyRegular k Λ)
    (N : ℕ) (hN : 0 < N)
    (hpower : IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ N ≤
      (Ideal.map α.toRingHom (singularIdeal k A)).map
        (algebraMap Λ (Localization.AtPrime q.asIdeal))) :
    ∃ (m : ℕ) (_ : Algebra (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k (MvPolynomial (Fin m) k) Λ)
      (C : Type (max u v)) (_ : CommRing C) (_ : Algebra k C)
      (_ : Algebra (MvPolynomial (Fin m) k) C)
      (_ : IsScalarTower k (MvPolynomial (Fin m) k) C)
      (_ : FinitePresentation (MvPolynomial (Fin m) k) C)
      (β : A →ₐ[k] C) (γ : C →ₐ[MvPolynomial (Fin m) k] Λ),
      (γ.restrictScalars k).comp β = α ∧ popescuIdeal α ≤ popescuIdeal γ ∧
      ∃ (r : ℕ) (π : Fin r → MvPolynomial (Fin m) k),
        1 ≤ r ∧
        (∀ i, algebraMap (MvPolynomial (Fin m) k) Λ (π i) ∈ q.asIdeal) ∧
        (∀ (i : Fin r)
          (x : MvPolynomial (Fin m) k ⧸ Ideal.span
            {y | ∃ j : Fin r, j.val < i.val ∧ y = π j ^ 8}),
          π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
        (∀ (i : Fin r)
          (x : Λ ⧸ Ideal.span
            {y | ∃ j : Fin r, j.val < i.val ∧
              y = algebraMap (MvPolynomial (Fin m) k) Λ (π j) ^ 8}),
          π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
        (∀ i, IsStrictlyStandardElement
          (R := MvPolynomial (Fin m) k) (algebraMap (MvPolynomial (Fin m) k) C (π i))) ∧
    let R := MvPolynomial (Fin m) k
    let J := Ideal.span (Set.range (fun i : Fin r ↦ π i ^ 8))
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
            (_ : IsScalarTower R (R ⧸ I₀) E),
            EssentiallySmooth (R ⧸ I₀) E ∧
            ∃ (a : C →ₐ[R] E) (b : E →ₐ[R] L ⧸ K),
              b.comp a = (Ideal.Quotient.mkₐ R K).comp
                ((IsScalarTower.toAlgHom R Λ L).comp γ) := by
  let L := Localization.AtPrime q.asIdeal
  let d := (IsLocalRing.maximalIdeal L).spanFinrank
  obtain ⟨s, gens, hgens, B, hB, hkB, hAB, hkAB, hSB, hkSB, P, hval, hrel,
    C₀, hC₀, hkC₀, hSC₀, hkSC₀, hfpC₀, β₀, ρ, c, hc, hρβ, hgeometry⟩ :=
    exists_popescu_universal_standardizer (k := k) (A := A) (Λ := Λ) d N hN
  let S := MvPolynomial (Fin d) k
  let : CommRing B := hB
  let : Algebra k B := hkB
  let : Algebra A B := hAB
  have : IsScalarTower k A B := hkAB
  let : Algebra S B := hSB
  have : IsScalarTower k S B := hkSB
  let : CommRing C₀ := hC₀
  let : Algebra k C₀ := hkC₀
  let : Algebra S C₀ := hSC₀
  have : IsScalarTower k S C₀ := hkSC₀
  have : FinitePresentation S C₀ := hfpC₀
  obtain ⟨m, hRΛ, hkRΛ, hSR, hkSR, hSΛ, hSRΛ, hkSΛ, η, π,
    hη, hπ, hmem, hkerR, hkerΛ, hsolution⟩ :=
    exists_popescu_parameter_solution p hp α q hreg N hN hpower d rfl
      s gens hgens B P hval hrel c hc
  let R := MvPolynomial (Fin m) k
  let : Algebra R Λ := hRΛ
  have : IsScalarTower k R Λ := hkRΛ
  let : Algebra S R := hSR
  have : IsScalarTower k S R := hkSR
  let : Algebra S Λ := hSΛ
  have : IsScalarTower S R Λ := hSRΛ
  have : IsScalarTower k S Λ := hkSΛ
  let C := R ⊗[S] C₀
  let β : A →ₐ[k] C :=
    (TensorProduct.includeRight.restrictScalars k).comp β₀
  let γ : C →ₐ[R] Λ := AlgHom.liftEquiv S R C₀ Λ (η.comp ρ)
  have hfactor : (γ.restrictScalars k).comp β = α := by
    ext x
    change γ (β x) = α x
    have hβ : β x = 1 ⊗ₜ[S] β₀ x := rfl
    rw [hβ]
    change (AlgHom.liftEquiv S R C₀ Λ (η.comp ρ)) (1 ⊗ₜ[S] β₀ x) = α x
    rw [AlgHom.liftEquiv_tmul]
    simp only [one_smul, AlgHom.comp_apply]
    have hρβx : ρ (β₀ x) = algebraMap A B x := AlgHom.congr_fun hρβ x
    exact (congrArg η hρβx).trans (AlgHom.congr_fun hη x)
  obtain ⟨hideal, hstandard⟩ := hgeometry R η
  refine ⟨m, hRΛ, hkRΛ, C, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, β, γ, hfactor, ?_, d + 1, π,
    Nat.le_add_left 1 d, hmem, hkerR, hkerΛ, ?_, ?_⟩
  · simpa only [hη] using hideal
  · intro i
    exact hstandard (π i) (hπ i)
  · dsimp only at hsolution ⊢
    obtain ⟨n, hn, hnil, I₀, K, hI₀, hK, hIK, t, D', hD', hlocal, hart,
      hRE, hquotE, htowerE, hSE, hSRE, hsmooth, θ, b, hθ⟩ := hsolution
    let : CommRing D' := hD'
    have : IsLocalRing D' := hlocal
    have : IsArtinianRing D' := hart
    let E := MvPolynomial (Fin t) D'
    let : Algebra R E := hRE
    let : Algebra (R ⧸ I₀) E := hquotE
    have : IsScalarTower R (R ⧸ I₀) E := htowerE
    let : Algebra S E := hSE
    have : IsScalarTower S R E := hSRE
    let a : C →ₐ[R] E := AlgHom.liftEquiv S R C₀ E (θ.comp ρ)
    refine ⟨n, hn, hnil, I₀, K, hI₀, hK, hIK, t, D', hD', hlocal, hart,
      hRE, hquotE, htowerE, hsmooth, a, b, ?_⟩
    apply TensorProduct.ext_ring
    ext x
    simp only [a, γ, AlgHom.coe_comp, AlgHom.coe_restrictScalars',
      Function.comp_apply, TensorProduct.includeRight_apply]
    rw [AlgHom.liftEquiv_tmul, AlgHom.liftEquiv_tmul]
    simp only [one_smul, AlgHom.comp_apply]
    change b (θ (ρ x)) = _
    exact AlgHom.congr_fun hθ (ρ x)


end Algebra
