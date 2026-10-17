/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.Abhyankar
public import WeilConjectures.RingTheory.Etale.DepthTwo.SmoothPurity
public import WeilConjectures.RingTheory.Etale.DepthTwo.Spreading

/-!
# Étaleness of the normalization near a section over a trait

Let `R₀` be a Noetherian integrally closed domain with fraction field `K`, `q` a prime of `R₀` of
height one (so that `(R₀)_q` is a discrete valuation ring), `B` a smooth `R₀`-algebra with an
`R₀`-algebra section `ε : B → R₀`, `B_K` the localization of `B` at the nonzero elements of `R₀`,
and `L` a finite étale `B_K`-algebra which is Galois with group `G` (`G` acts by `B_K`-algebra
automorphisms, `L` has rank `|G|` everywhere and `L^G = B_K`), with `|G|` invertible in `R₀`.
If `L` has `|G|` distinct ring maps to `K` over `ε` (the cover is split along the section), then
the integral closure of `B` in `L` is étale over a neighbourhood of the prime `P = ε⁻¹(q)`
(`Algebra.exists_etale_integralClosure_of_height_eq_one`).

This is the trait case of the proof of [Stacks 0EYJ], a step of blueprint
`sbc-thm-spreading-finite-etale-galois`. Proof: adjoin a primitive `n`-th root of unity
(`n = |G|`, an étale extension `A₁` of `A = (R₀)_q`) and an `n`-th root `t` of a uniformizer
(`A₂ = A₁[t]/(tⁿ - π)`, a discrete valuation ring). By Abhyankar's lemma
(`IsDiscreteValuationRing.etale_integralClosure_adjoinRoot`) the normalization `T₂` of
`B₂ = B ⊗ A₂` in `L ⊗ K₂` is étale at the generic points of the closed fibre, hence near the
section by purity (`RingTheory.DepthTwo.exists_etale_integralClosure_of_smooth`). Along the
section `T₂` is split, and the `|G|` points lift to the completion `R₂^` of the local ring at the
section; by uniqueness of the lifts they are invariant under `Γ = Gal(K₂/K₁) ≅ μₙ`. Taking
`Γ`-invariants (`n` is invertible) gives `R₁^ ⊗ T₁ ≅ (R₁^)^{|G|}` for the normalization `T₁` of
`B ⊗ A₁`, so `T₁`, hence the normalization of `B`, is étale near the section.
-/

@[expose] public section

universe u

open TensorProduct

namespace Algebra

variable {R₀ B Bk L : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
  [IsNoetherianRing R₀]
  [CommRing B] [Algebra R₀ B] [Algebra.Smooth R₀ B] [IsNoetherianRing B]
  [CommRing Bk] [Algebra B Bk]
  [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)) Bk]
  [CommRing L] [Algebra Bk L] [Algebra B L] [IsScalarTower B Bk L]
  [Module.Finite Bk L] [Algebra.Etale Bk L]

include Bk in
/-- **Étaleness of the normalization at a section over a trait**, local form: the base change of
the integral closure of `B` in `L` to the local ring `B_P`, `P = ε⁻¹(q)`, is finite étale.

TODO (gap): reduce to `Algebra.etale_localization_integralClosure_of_isPrimitiveRoot` by the base
change to the discrete valuation ring `A₁` of `IsDiscreteValuationRing.exists_etale_isPrimitiveRoot`
over `(R₀)_q` (a DVR by `IsLocalization.AtPrime.isDiscreteValuationRing_of_height_eq_one`):
`B₁ = A₁ ⊗ B`, `Bk₁ = A₁ ⊗ Bk` (`IsLocalization.tensorProduct_tensorProduct` and
`IsLocalization.of_le_of_exists_dvd`), `L₁ = Bk₁ ⊗[Bk] L` with the `G`-action on the second factor
(fixed points by `AlgHom.mem_range_algebraMap_of_forall_baseChange_eq`), and points `φⱼ ⊗ K₁`.
The closure commutes with the base change (`TensorProduct.toIntegralClosure_bijective_of_tower`),
and finite étaleness descends along `B_P → (B₁)_{P₁}` (`Algebra.etale_and_finite_of_isLocalHom`). -/
theorem etale_localization_integralClosure_of_height_eq_one (ε : B →ₐ[R₀] R₀) (q : Ideal R₀)
    [q.IsPrime] (hq : q.height = 1) (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G L] [SMulCommClass G Bk L]
    (hfix : ∀ x : L, (∀ g : G, g • x = x) → x ∈ Set.range (algebraMap Bk L))
    (hrank : ∀ p, Module.rankAtStalk (R := Bk) L p = Nat.card G)
    (hG : IsUnit (Nat.card G : R₀))
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (φ : Fin (Nat.card G) → (L →+* K))
    (hφ : ∀ j, (φ j).comp (algebraMap B L) = (algebraMap R₀ K).comp ε.toRingHom)
    (hφinj : Function.Injective φ) :
    Algebra.Etale (Localization.AtPrime (q.comap ε))
        (Localization.AtPrime (q.comap ε) ⊗[B] integralClosure B L) ∧
      Module.Finite (Localization.AtPrime (q.comap ε))
        (Localization.AtPrime (q.comap ε) ⊗[B] integralClosure B L) := by
  sorry

include Bk in
/-- **Étaleness of the normalization near a section over a trait** (trait case of the proof of
[Stacks 0EYJ], a step of blueprint `sbc-thm-spreading-finite-etale-galois`). See the module
docstring. -/
theorem exists_etale_integralClosure_of_height_eq_one (ε : B →ₐ[R₀] R₀) (q : Ideal R₀)
    [q.IsPrime] (hq : q.height = 1) (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G L] [SMulCommClass G Bk L]
    (hfix : ∀ x : L, (∀ g : G, g • x = x) → x ∈ Set.range (algebraMap Bk L))
    (hrank : ∀ p, Module.rankAtStalk (R := Bk) L p = Nat.card G)
    (hG : IsUnit (Nat.card G : R₀))
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (φ : Fin (Nat.card G) → (L →+* K))
    (hφ : ∀ j, (φ j).comp (algebraMap B L) = (algebraMap R₀ K).comp ε.toRingHom)
    (hφinj : Function.Injective φ) :
    ∃ g ∉ q.comap ε, ∀ (B' L' : Type u) [CommRing B'] [CommRing L'] [Algebra B B']
      [IsLocalization.Away g B'] [Algebra L L'] [IsLocalization.Away (algebraMap B L g) L']
      [Algebra B' L'] [Algebra B L'] [IsScalarTower B B' L'] [IsScalarTower B L L'],
      Algebra.Etale B' (integralClosure B' L') := by
  obtain ⟨hE, hF⟩ := etale_localization_integralClosure_of_height_eq_one (Bk := Bk) ε q hq G
    hfix hrank hG φ hφ hφinj
  exact Algebra.exists_etale_integralClosure_of_etale_localization (R := R₀) (Bk := Bk)
    (q.comap ε) hE hF

end Algebra
