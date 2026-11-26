/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PopescuResolution
import WeilConjectures.RingTheory.PopescuCharPPreparation
import WeilConjectures.RingTheory.PopescuDelocalizeHeightZero
import WeilConjectures.RingTheory.PopescuLiftSolution
import WeilConjectures.RingTheory.FactorsThroughSmooth

/-!
# Resolving Popescu's local problem in positive characteristic

Popescu's local problem over a field of positive characteristic is resolvable when the target
is Noetherian and geometrically regular and the prime is minimal over the extended singular
ideal.

## Implementation details

The argument follows the proof of Stacks Lemma 07FJ, with the following corrections to the
source:

* the generators are taken of `H_{A/k}` (Stacks writes `H_{A/R}`);
* the exponent is `n = N + d e` with `e = 8c`, since `n = N + d c` does not give
  `p^n k[y]_p ⊆ (π_1^e, …, π_d^e)`;
* the polynomial ring is `k[y_1, …, y_m, t_1, …, t_d]` (Stacks writes `t_1, …, t_m`), and the
  parameters `π_i` are taken in `k[y]`;
* the minimality hypothesis is checked after reducing modulo `(γ_1^e, …, γ_d^e)`;
* the final map sends `z_ij` to `λ̄_ij t_i^(2N) δ̄_i^(-2N)` rather than to `λ_ij`, so that it is
  compatible with `k[x] → R_0[t]`.

## References

* [Stacks, Tag 07FJ]
-/

@[expose] public section

universe u v w

namespace Algebra

private theorem singularIdeal_eq_top_of_smooth
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    [Smooth R B] : singularIdeal R B = ⊤ := by
  apply top_unique
  rw [← Ideal.span_singleton_one]
  apply Ideal.span_le.mpr
  intro x hx
  have hx1 : x = 1 := by simpa using hx
  subst x
  apply Ideal.le_radical
  apply Ideal.subset_span
  change Smooth R (Localization.Away (1 : B))
  let : Smooth B (Localization.Away (1 : B)) := Smooth.of_isLocalization_Away 1
  exact Smooth.comp R B _

private theorem popescuIdeal_eq_top_of_smooth
    {R : Type u} {B : Type v} {Λ : Type w}
    [CommRing R] [CommRing B] [CommRing Λ] [Algebra R B] [Algebra R Λ]
    [Smooth R B] (γ : B →ₐ[R] Λ) : popescuIdeal γ = ⊤ := by
  unfold popescuIdeal
  rw [singularIdeal_eq_top_of_smooth R B, Ideal.map_top, Ideal.radical_top]

private theorem resolved_of_ideal_not_le
    {R : Type u} {C : Type (max u v)} {Λ : Type w}
    [CommRing R] [CommRing C] [CommRing Λ] [Algebra R C] [Algebra R Λ]
    [IsNoetherianRing R] [FinitePresentation R C]
    (γ : C →ₐ[R] Λ) (q : PrimeSpectrum Λ) (h : ¬ popescuIdeal γ ≤ q.asIdeal) :
    CanBePopescuResolved γ q := by
  exact ⟨C, inferInstance, inferInstance, AlgHom.id R C, γ,
    inferInstance, γ.comp_id, le_rfl, h⟩

private theorem resolved_of_essentiallySmooth_factorization
    {R : Type u} {C E : Type (max u v)} {Λ : Type w}
    [CommRing R] [CommRing C] [CommRing E] [CommRing Λ]
    [Algebra R C] [Algebra R E] [Algebra R Λ]
    [IsNoetherianRing R] [FinitePresentation R C]
    (γ : C →ₐ[R] Λ) (q : PrimeSpectrum Λ)
    (hE : EssentiallySmooth R E) (f : C →ₐ[R] E) (g : E →ₐ[R] Λ)
    (hfg : g.comp f = γ) : CanBePopescuResolved γ q := by
  obtain ⟨T, instT, algT, hT, a, b, hab⟩ :=
    essentiallySmooth_factors_through_smooth R C E hE f
  let := instT
  let := algT
  let := hT
  refine ⟨T, inferInstance, inferInstance, a, g.comp b, inferInstance, ?_, ?_, ?_⟩
  · rw [AlgHom.comp_assoc, hab, hfg]
  · rw [popescuIdeal_eq_top_of_smooth (g.comp b)]
    exact le_top
  · rw [popescuIdeal_eq_top_of_smooth]
    exact fun h ↦ q.isPrime.ne_top (top_le_iff.mp h)

private theorem popescuIdeal_restrictScalars_le
    {k : Type u} {R : Type u} {B : Type v} {Λ : Type w}
    [CommRing k] [CommRing R] [CommRing B] [CommRing Λ]
    [Algebra k R] [Algebra k B] [Algebra k Λ] [Algebra R B] [Algebra R Λ]
    [IsScalarTower k R B] [IsScalarTower k R Λ] [Smooth k R]
    (γ : B →ₐ[R] Λ) : popescuIdeal γ ≤ popescuIdeal (γ.restrictScalars k) := by
  apply Ideal.radical_mono
  apply Ideal.map_mono
  apply Ideal.radical_mono
  apply Ideal.span_mono
  intro x hx
  change Smooth k (Localization.Away x)
  let : Smooth R (Localization.Away x) := hx
  exact Smooth.comp k R _

/-- Popescu's local problem over a positive-characteristic field is resolvable when the target
is Noetherian and geometrically regular and the prime is minimal over the extended singular
ideal. -/
theorem canBePopescuResolved_of_char_pos
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (hreg : IsGeometricallyRegular k Λ)
    (hminimal : q.asIdeal ∈ (popescuIdeal α).minimalPrimes) :
    CanBePopescuResolved α q := by
  obtain ⟨m, algΛ, towerΛ, C, ringC, algkC, algRC, towerC, fpC, β, γ,
    hcomp, hdom, r, π, hr, hπ, hR, hΛ, hstandard, fp₀, γ₀, q₀, hγ₀, hq₀, hlocal⟩ :=
    exists_popescu_char_p_preparation p hp α q hreg hminimal
  let R := MvPolynomial (Fin m) k
  let : Smooth k R := ⟨inferInstance, inferInstance⟩
  let := algΛ
  let := towerΛ
  let := ringC
  let := algkC
  let := algRC
  let := towerC
  let := fpC
  let J := Ideal.span (Set.range (fun i : Fin r ↦ π i ^ 8))
  let J_C := J.map (algebraMap R C)
  let J_Λ := J.map (algebraMap R Λ)
  let R₀ := R ⧸ J
  let C₀ := C ⧸ J_C
  let Λ₀ := Λ ⧸ J_Λ
  let := fp₀
  have hresolved₀ : CanBePopescuResolved γ₀ q₀ := by
    rcases hlocal with hout | ⟨hmin₀, hdim₀, hfactor⟩
    · exact resolved_of_ideal_not_le γ₀ q₀ hout
    · apply canBePopescuResolved_of_local_height_zero γ₀ q₀ hmin₀ _ hdim₀
      let P := Localization.AtPrime (q₀.asIdeal.under R₀)
      let L := Localization.AtPrime q₀.asIdeal
      let := Localization.AtPrime.algebraOfLiesOver
        (q₀.asIdeal.under R₀) q₀.asIdeal
      obtain ⟨E, ringE, algE, hE, f, g, hfg⟩ := hfactor
      let := ringE
      let := algE
      exact resolved_of_essentiallySmooth_factorization _ _ hE f g hfg
  have hresolved : CanBePopescuResolved γ q :=
    canBePopescuResolved_of_quotient_eighth_powers r π γ q hr hπ hR hΛ hstandard
      ⟨fp₀, γ₀, q₀, hγ₀, hq₀, hresolved₀⟩
  obtain ⟨B, ringB, algRB, a, b, hfpB, hab, hCB, hout⟩ := hresolved
  let := ringB
  let := algRB
  let : Algebra k B := ((algebraMap R B).comp (algebraMap k R)).toAlgebra
  let : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' rfl
  let := hfpB
  let : FinitePresentation k B := FinitePresentation.trans k R B
  refine ⟨B, inferInstance, inferInstance, (a.restrictScalars k).comp β,
    b.restrictScalars k, inferInstance, ?_, ?_, ?_⟩
  · ext x
    have h := AlgHom.congr_fun hab (β x)
    have h' := AlgHom.congr_fun hcomp x
    exact h.trans h'
  · exact hdom.trans (hCB.trans (popescuIdeal_restrictScalars_le b))
  · exact fun h ↦ hout ((popescuIdeal_restrictScalars_le b).trans h)

end Algebra
