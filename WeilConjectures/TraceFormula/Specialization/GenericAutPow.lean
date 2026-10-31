/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelAutGalois
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisTameSylow
public import WeilConjectures.FieldTheory.Galois.PowSurjective

/-!

# The pro-`p` kernel `P'` is divisible by integers prime to `p`

Let `F = k'((t))`, `F_K = K((t))` with `K` algebraically closed, `Ω_K = F_K^alg`,
`L' = F_K·F^sep ⊆ Ω_K` (`AlgebraicGeometry.traitGenericSepCompositum`) and `S = L'^sep ⊆ Ω_K`.
Every finite Galois extension of `L'` has `p`-power degree
(`AlgebraicGeometry.isPGroup_traitGenericSepCompositum_of_dvd`), so every element of
`Gal(S / L')` is an `n`-th power for `p ∤ n`
(`AlgebraicGeometry.exists_pow_eq_separableClosure_traitGenericSepCompositum`).

The group `P'` of generic automorphisms (`NearbyCyclesModel.GenericAut`), the automorphisms of
`Ω_K` over `F_K` fixing the image of `Ω = F^alg`, maps bijectively onto `Gal(S / L')`: an
automorphism of `Ω_K` is determined by its restriction to `S`, as `Ω_K / S` is purely
inseparable, and every automorphism of `S` over `L'` extends to `Ω_K` and then fixes `Ω`, which is
purely inseparable over `F^sep`. Hence every generic automorphism is an `n`-th power for `p ∤ n`
(`NearbyCyclesModel.GenericAut.exists_pow_eq`). This is the divisibility of `P'` by powers of
`ℓ ≠ p` used for the finiteness of its action on `ℚ̄_ℓ`-nearby cycles (SGA 4½, [Th. finitude],
§3.7; `NearbyCyclesModel.autAction_baseChangeAut_eq_id_of_distinguished`).

-/

@[expose] public section

universe u

open IntermediateField

namespace AlgebraicGeometry

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] [IsAlgClosed K]

/-- **`n`-th roots in `Gal(L'^sep / L')`**: every element of the Galois group of the separable
closure of `L' = F_K·F^sep` in `Ω_K` is an `n`-th power, for `n` prime to the characteristic
exponent `p`. -/
theorem exists_pow_eq_separableClosure_traitGenericSepCompositum {p : ℕ} (hp : p.Prime)
    (hpk : ∀ n : ℕ, (n : k') = 0 → p ∣ n) {n : ℕ} (hn : ¬ p ∣ n)
    (σ : Gal(separableClosure (traitGenericSepCompositum k' K) (traitGenericField K) /
      traitGenericSepCompositum k' K)) : ∃ τ, τ ^ n = σ := by
  have := Fact.mk hp
  have : Normal (FractionRing (PowerSeries K)) (traitGenericField K) := inferInstance
  have : Normal (traitGenericSepCompositum k' K) (traitGenericField K) :=
    Normal.tower_top_of_normal (FractionRing (PowerSeries K)) _ _
  refine IsGalois.exists_pow_eq_separableClosure (fun M _ _ ↦ ?_) σ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_traitGenericSepCompositum_of_dvd hp hpk M)
  rw [← IsGalois.card_aut_eq_finrank, hk]
  exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.GenericAut

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

/-- Generic automorphisms fix `L' = F_K·F^sep`. -/
lemma toAlgEquiv_apply_of_mem_traitGenericSepCompositum (σ : GenericAut k' K)
    {x : traitGenericField K} (hx : x ∈ traitGenericSepCompositum k' K) :
    toAlgEquiv σ x = x := by
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨y, -, rfl⟩ := hx
    exact toRingAut_traitGenericFieldMap σ y
  | algebraMap x => exact (toAlgEquiv σ).commutes x
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

/-- `n`-th powers of the restrictions of scalars of an automorphism. -/
lemma _root_.AlgEquiv.restrictScalars_pow_apply {R A B : Type*} [CommSemiring R] [CommSemiring A]
    [Semiring B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] (f : B ≃ₐ[A] B)
    (n : ℕ) (z : B) : ((f.restrictScalars R) ^ n) z = (f ^ n) z := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih]; rfl

variable [IsAlgClosed K]

/-- **The pro-`p` kernel `P'` is divisible by integers prime to `p`**: every generic
automorphism is an `n`-th power for `n` prime to the characteristic exponent `p`. -/
theorem exists_pow_eq {p : ℕ} (hp : p.Prime) (hpk : ∀ n : ℕ, (n : k') = 0 → p ∣ n) {n : ℕ}
    (hn : ¬ p ∣ n) (σ : GenericAut k' K) : ∃ τ, τ ^ n = σ := by
  let L' := traitGenericSepCompositum k' K
  have : Normal (FractionRing (PowerSeries K)) (traitGenericField K) := inferInstance
  have : Normal L' (traitGenericField K) :=
    Normal.tower_top_of_normal (FractionRing (PowerSeries K)) _ _
  have : Algebra.IsAlgebraic L' (traitGenericField K) :=
    Algebra.IsAlgebraic.tower_top (K := FractionRing (PowerSeries K)) L'
  let S := separableClosure L' (traitGenericField K)
  let e : traitGenericField K ≃ₐ[L'] traitGenericField K :=
    { toRingEquiv := (toAlgEquiv σ).toRingEquiv
      commutes' := fun x ↦ toAlgEquiv_apply_of_mem_traitGenericSepCompositum σ x.2 }
  obtain ⟨h, hh⟩ := exists_pow_eq_separableClosure_traitGenericSepCompositum hp hpk hn
    (e.restrictNormal S)
  let h' : traitGenericField K ≃ₐ[L'] traitGenericField K := h.liftNormal _
  have hres : (h' ^ n).restrictNormal S = e.restrictNormal S := by
    have h₁ : AlgEquiv.restrictNormalHom S (h' ^ n) = (AlgEquiv.restrictNormalHom S h') ^ n :=
      map_pow _ _ _
    have h₂ : AlgEquiv.restrictNormalHom S h' = h := h.restrict_liftNormal (traitGenericField K)
    exact h₁.trans (by rw [h₂, hh])
  have hh' : h' ^ n = e := by
    refine AlgEquiv.ext_of_isPurelyInseparable S (fun s hs ↦ ?_)
    have h₁ := AlgEquiv.restrictNormal_commutes (h' ^ n) S ⟨s, hs⟩
    have h₂ := AlgEquiv.restrictNormal_commutes e S ⟨s, hs⟩
    rw [hres] at h₁
    exact h₁.symm.trans h₂
  let q := ringExpChar (traitGenericField K)
  have : ExpChar (traitGenericField k') q :=
    (traitGenericFieldMap k' K).expChar (traitGenericFieldMap k' K).injective q
  have : ExpChar (separableClosure (FractionRing (PowerSeries k')) (traitGenericField k')) q :=
    (algebraMap _ (traitGenericField k')).expChar Subtype.val_injective q
  have hfix : ∀ y, (h'.restrictScalars (FractionRing (PowerSeries K)))
      (traitGenericFieldMap k' K y) = traitGenericFieldMap k' K y := by
    intro y
    obtain ⟨m, s, hs⟩ := IsPurelyInseparable.pow_mem
      (separableClosure (FractionRing (PowerSeries k')) (traitGenericField k')) q y
    have hmem : traitGenericFieldMap k' K (y ^ q ^ m) ∈ L' := by
      rw [← hs]
      exact subset_adjoin _ _ ⟨s, s.2, rfl⟩
    have h₁ : h' (traitGenericFieldMap k' K (y ^ q ^ m)) =
        traitGenericFieldMap k' K (y ^ q ^ m) :=
      h'.commutes ⟨_, hmem⟩
    rw [map_pow, map_pow] at h₁
    exact iterateFrobenius_inj (traitGenericField K) q m h₁
  refine ⟨ofAlgEquiv _ hfix, toAlgEquiv_injective ?_⟩
  rw [map_pow, toAlgEquiv_ofAlgEquiv]
  refine AlgEquiv.ext fun z ↦ ?_
  rw [AlgEquiv.restrictScalars_pow_apply, hh']
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.GenericAut
