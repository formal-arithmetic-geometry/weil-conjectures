/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.RingTheory.Unramified.Basic
import WeilConjectures.RingTheory.ConormalComplementPolynomialLift
/-!
# Existence and lifting for universal first order thickenings

We show that a formally unramified algebra admits a universal first order thickening.

## Implementation details

Present `S` as `P/J` with `P` the polynomial algebra on generators indexed by `S`. The conormal
map `d : J/J² → S ⊗[P] Ω[P/R]` is surjective with free target, so it splits; with `J'` the inverse
image of the splitting's image, `S' = P/J'` is the thickening. Lifts are adjusted by derivations,
parametrized by `S`-linear maps out of `S ⊗[P] Ω[P/R]`.

## References

* [Stacks Project, Lemma 04EB](https://stacks.math.columbia.edu/tag/04EB)
-/
@[expose] public section
universe u
namespace Algebra
/-- A formally unramified algebra admits a surjection with square-zero kernel having the
universal unique lifting property. Uniqueness of the thickening is not asserted here. -/
theorem exists_universalFirstOrderThickening_core
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [FormallyUnramified R S] :
    ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra R S') (π : S' →ₐ[R] S),
      Function.Surjective π ∧ RingHom.ker π.toRingHom ^ 2 = ⊥ ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A] (I : Ideal A), I ^ 2 = ⊥ →
        ∀ a : S →ₐ[R] A ⧸ I,
          ∃! a' : S' →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp a' = a.comp π) := by
  classical
  let G := Generators.self R S
  let P := G.toExtension
  have hd : Function.Surjective P.cotangentComplex := by
    intro w
    exact (P.exact_cotangentComplex_toKaehler w).mp (Subsingleton.elim _ _)
  obtain ⟨σ, hσ⟩ := P.cotangentComplex.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hd)
  have hσ_apply (w : P.CotangentSpace) : P.cotangentComplex (σ w) = w :=
    DFunLike.congr_fun hσ w
  let N := (LinearMap.range σ).restrictScalars P.Ring
  let Q := N.comap (Extension.Cotangent.mk (P := P))
  let K : Ideal P.Ring := Q.map P.ker.subtype
  have hK : K ≤ P.ker := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hmem (x : P.ker) : x.val ∈ K ↔ Extension.Cotangent.mk x ∈ N := by
    constructor
    · rintro ⟨y, hy, heq⟩
      have : y = x := Subtype.ext heq
      simpa [Q, this] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hKsq : P.ker ^ 2 ≤ K := by
    intro x hx
    have hxJ : x ∈ P.ker := Ideal.pow_le_self (by decide) hx
    apply (hmem ⟨x, hxJ⟩).mpr
    rw [(Extension.Cotangent.mk_eq_zero_iff _).mpr hx]
    exact N.zero_mem
  have hsurj : ∀ w : P.CotangentSpace,
      ∃ x : P.ker, x.val ∈ K ∧ P.cotangentComplex (Extension.Cotangent.mk x) = w := by
    intro w
    obtain ⟨x, hx⟩ := Extension.Cotangent.mk_surjective (σ w)
    refine ⟨x, (hmem x).mpr ?_, ?_⟩
    · change Extension.Cotangent.mk x ∈ LinearMap.range σ
      exact ⟨w, hx.symm⟩
    · rw [hx, hσ_apply]
  have hinj : ∀ x : P.ker, x.val ∈ K →
      P.cotangentComplex (Extension.Cotangent.mk x) = 0 → x.val ∈ P.ker ^ 2 := by
    intro x hx hdx
    obtain ⟨w, hw⟩ := (hmem x).mp hx
    have hw0 : w = 0 := by rw [← hσ_apply w, hw, hdx]
    apply (Extension.Cotangent.mk_eq_zero_iff _).mp
    rw [← hw, hw0, map_zero]
  let p : P.Ring →ₐ[R] S := IsScalarTower.toAlgHom R P.Ring S
  have hzero : ∀ x : P.Ring, x ∈ K → p x = 0 :=
    fun x hx => RingHom.mem_ker.mp (hK hx)
  let π : P.Ring ⧸ K →ₐ[R] S := Ideal.Quotient.liftₐ K p hzero
  have hπ : π.comp (Ideal.Quotient.mkₐ R K) = p := Ideal.Quotient.liftₐ_comp ..
  refine ⟨P.Ring ⧸ K, inferInstance, inferInstance, π, ?_, ?_, ?_⟩
  · intro s
    obtain ⟨x, hx⟩ := P.algebraMap_surjective s
    exact ⟨Ideal.Quotient.mk K x, (AlgHom.congr_fun hπ x).trans hx⟩
  · change RingHom.ker (Ideal.Quotient.lift K p.toRingHom hzero) ^ 2 = ⊥
    rw [Ideal.ker_quotient_lift p.toRingHom hK, ← Ideal.map_pow,
      Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact hKsq
  · intro A _ _ I hI a
    obtain ⟨β, hβ, huniq⟩ := conormalComplement_polynomial_lift
      R S G K hK hsurj hinj A I hI a
    let f : P.Ring ⧸ K →ₐ[R] A := Ideal.Quotient.liftₐ K β hβ.2
    have hf : f.comp (Ideal.Quotient.mkₐ R K) = β := Ideal.Quotient.liftₐ_comp ..
    refine ⟨f, ?_, ?_⟩
    · apply Ideal.Quotient.algHom_ext
      rw [AlgHom.comp_assoc, hf, AlgHom.comp_assoc, hπ]
      exact hβ.1
    · intro g hg
      apply Ideal.Quotient.algHom_ext
      rw [hf]
      apply huniq
      constructor
      · rw [← AlgHom.comp_assoc, hg, AlgHom.comp_assoc, hπ]
        rfl
      · intro x hx
        change P.Ring at x
        change g (Ideal.Quotient.mk K x) = 0
        have hx0 : Ideal.Quotient.mk K x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
        exact (congrArg g hx0).trans (map_zero g)
end Algebra
