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

import WeilConjectures.RingTheory.PopescuCharPPreparationGlobal
import WeilConjectures.RingTheory.EssentiallySmoothBaseChange
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Popescu characteristic-p preparation: auxiliary construction

The construction steps of the positive characteristic case of the local resolution step in
Popescu's theorem, up to a factorization at an auxiliary thickening.

## Implementation details

With `N` such that `q^N Λ_q ⊆ H_{A/k} Λ_q`, generators `a_j` of `H_{A/k}` and `d = dim Λ_q`, the
algebra `B = A[x_i, z_ij] / (x_i^(2N) - ∑_j z_ij a_j)` is improved to a retract `C` with free
differentials on the relevant opens, and `x_i^c` is strictly standard. The solution modulo `q^n`
gives a regular system of parameters `π_i`, which Ogoma's lemma rescales so that the annihilator
conditions hold; enlarging the Artinian solution gives units `δ_i` and `λ_ij` with
`(δ_i π_i)^(2N) = ∑_j a_j λ_ij`. When `d = 0` the parameter list is padded by a zero. All
constructed algebras have representatives in `Type (max u v)`.

The Stacks Project text contains some misprints corrected here: the singular ideal is
`H_{A/k}` rather than `H_{A/R}`, the variables of `R` are `t_1, …, t_d`, and the exponent is
`n = N + d e` with `e = 8 c` rather than `N + d c`, which is needed for
`p^n k[y]_p ⊆ (π_1^e, …, π_d^e)`.

## References

* [Stacks, Tag 07FJ] (construction and quotient steps)
* [Stacks, Tag 07FH]
* [Stacks, Tag 07FI]
-/

@[expose] public section
universe u v w
open scoped TensorProduct
namespace Algebra

/-- Construct the standardized polynomial-base algebra and a factorization at an auxiliary
thickening, with explicit power and ideal-containment witnesses. -/
theorem exists_popescu_char_p_preparation_core
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (hreg : IsGeometricallyRegular k Λ)
    (hminimal : q.asIdeal ∈ (popescuIdeal α).minimalPrimes) :
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
      ∃ (I : Ideal Q) (K : Ideal L),
        I ≤ JQ ∧ K ≤ JL ∧ I.map (algebraMap Q L) ≤ K ∧
        ∃ (D : Type (max u v)) (_ : CommRing D) (_ : Algebra Q D)
          (_ : Algebra (Q ⧸ I) D) (_ : IsScalarTower Q (Q ⧸ I) D),
          EssentiallySmooth (Q ⧸ I) D ∧
          ∃ (f : Q ⊗[R] C →ₐ[Q] D) (g : D →ₐ[Q] L ⧸ K),
            g.comp f = Algebra.TensorProduct.lift (Algebra.ofId Q (L ⧸ K))
              ((Ideal.Quotient.mkₐ R K).comp
                ((IsScalarTower.toAlgHom R Λ L).comp γ))
              (fun _ _ ↦ Commute.all _ _) := by
  let H := Ideal.map α.toRingHom (singularIdeal k A)
  let L₀ := Localization.AtPrime q.asIdeal
  have hmin : q.asIdeal ∈ H.minimalPrimes := by
    simpa only [popescuIdeal, Ideal.radical_minimalPrimes] using hminimal
  have hrad : (H.map (algebraMap Λ L₀)).radical = IsLocalRing.maximalIdeal L₀ := by
    rw [IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes L₀ q.asIdeal H hmin,
      Localization.AtPrime.map_eq_maximalIdeal]
  obtain ⟨N₀, hN₀⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (le_of_eq hrad.symm) (IsNoetherian.noetherian _)
  have hpower : IsLocalRing.maximalIdeal L₀ ^ (N₀ + 1) ≤ H.map (algebraMap Λ L₀) :=
    (Ideal.pow_le_pow_right (Nat.le_succ N₀)).trans hN₀
  obtain ⟨m, algΛ, towerΛ, C, ringC, algkC, algRC, towerC, fpC, β, γ,
    hcomp, hsing, r, π, hr, hπq, hannR, hannΛ, hstrict, hglobal⟩ :=
    exists_popescu_char_p_preparation_global p hp α q hreg (N₀ + 1) (by omega) hpower
  let := algΛ
  let := towerΛ
  let := ringC
  let := algkC
  let := algRC
  let := towerC
  let := fpC
  refine ⟨m, algΛ, towerΛ, C, ringC, algkC, algRC, towerC, fpC, β, γ,
    hcomp, hsing, r, π, hr, hπq, hannR, hannΛ, hstrict, ?_⟩
  let R := MvPolynomial (Fin m) k
  let Q := Localization.AtPrime (q.asIdeal.under R)
  let L := Localization.AtPrime q.asIdeal
  let := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  obtain ⟨n, hn, hpow, I₀, K, hI, hK, hIK, t, D', ringD', localD', artD',
    algRE, algIE, towerE, hE, a, b, hab⟩ := hglobal
  let := ringD'
  let := localD'
  let := artD'
  let E := MvPolynomial (Fin t) D' 
  let := algRE
  let := algIE
  let := towerE
  let I := I₀.map (algebraMap R Q)
  let : Algebra (R ⧸ I₀) (Q ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
      I₀ ≤ I.comap (algebraMap R Q))
  have : IsScalarTower R (R ⧸ I₀) (Q ⧸ I) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra (Q ⧸ I) (L ⧸ K) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp hIK)
  have : IsScalarTower Q (Q ⧸ I) (L ⧸ K) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra (R ⧸ I₀) (L ⧸ K) :=
    ((algebraMap (Q ⧸ I) (L ⧸ K)).comp (algebraMap (R ⧸ I₀) (Q ⧸ I))).toAlgebra
  have : IsScalarTower (R ⧸ I₀) (Q ⧸ I) (L ⧸ K) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R (R ⧸ I₀) (L ⧸ K) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap R (L ⧸ K) r =
        Ideal.Quotient.mk K (algebraMap Q L (algebraMap R Q r))
      rw [← IsScalarTower.algebraMap_apply R Q L]
      rfl
  let D := (Q ⧸ I) ⊗[R ⧸ I₀] E
  let : Algebra Q D := Algebra.TensorProduct.leftAlgebra
    (R := R ⧸ I₀) (S := Q) (A := Q ⧸ I) (B := E)
  let : Algebra R D := Algebra.TensorProduct.leftAlgebra
    (R := R ⧸ I₀) (S := R) (A := Q ⧸ I) (B := E)
  have : IsScalarTower Q (Q ⧸ I) D := inferInstance
  have : IsScalarTower R Q D := inferInstance
  have : IsScalarTower R (R ⧸ I₀) D := inferInstance
  let j : E →ₐ[R] D :=
    (Algebra.TensorProduct.includeRight (R := R ⧸ I₀) (A := Q ⧸ I)).restrictScalars R
  let f : Q ⊗[R] C →ₐ[Q] D :=
    Algebra.TensorProduct.lift (Algebra.ofId Q D) (j.comp a) (fun _ _ ↦ Commute.all _ _)
  let b' : E →ₐ[R ⧸ I₀] L ⧸ K :=
    b.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  let g : D →ₐ[Q] L ⧸ K :=
    (Algebra.TensorProduct.lift (Algebra.ofId (Q ⧸ I) (L ⧸ K)) b'
      (fun _ _ ↦ Commute.all _ _)).restrictScalars Q
  have hD : EssentiallySmooth (Q ⧸ I) D := essentiallySmooth_baseChange hE
  refine ⟨n, hn, hpow, I, K, hI, hK, hIK, D, inferInstance, inferInstance,
    inferInstance, inferInstance, hD, f, g, ?_⟩
  ext y
  change g (f (1 ⊗ₜ[R] y)) = _
  have hf : f (1 ⊗ₜ[R] y) = (1 ⊗ₜ[R ⧸ I₀] a y) := by
    change algebraMap Q D 1 * (1 ⊗ₜ[R ⧸ I₀] a y) = _
    simp
  rw [hf]
  change algebraMap (Q ⧸ I) (L ⧸ K) 1 * b' (a y) = _
  rw [map_one, one_mul]
  change b (a y) = _
  simpa only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul,
    map_one, one_mul] using DFunLike.congr_fun hab y

end Algebra
