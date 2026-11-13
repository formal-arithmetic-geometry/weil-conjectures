/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Smooth.Kaehler

/-! # Conormal residue kernel comparison

## References

* [Stacks Project, Tag 02HT](https://stacks.math.columbia.edu/tag/02HT)
-/

@[expose] public section

universe u

namespace Algebra

private theorem truncated_factor_ker
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Extension.{u} R S) (J L : Ideal P.Ring) :
    RingHom.ker (Ideal.Quotient.factorₐ R
      (sup_le_sup (Ideal.pow_le_self (I := J) (by decide : 2 ≠ 0)) (le_refl L))) =
        J.map (Ideal.Quotient.mk (J ^ 2 ⊔ L)) := by
  change RingHom.ker (Ideal.Quotient.factor
    (sup_le_sup (Ideal.pow_le_self (I := J) (by decide : 2 ≠ 0)) (le_refl L))) = _
  rw [Ideal.Quotient.factor, Ideal.ker_quotient_lift, Ideal.mk_ker, Ideal.map_sup]
  have hL : L.map (Ideal.Quotient.mk (J ^ 2 ⊔ L)) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact le_sup_right
  rw [hL, sup_bot_eq]

private theorem truncated_factor_ker_sq
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Extension.{u} R S) (J L : Ideal P.Ring) :
    (RingHom.ker (Ideal.Quotient.factorₐ R
      (sup_le_sup (Ideal.pow_le_self (I := J) (by decide : 2 ≠ 0)) (le_refl L)))) ^ 2 = ⊥ := by
  rw [truncated_factor_ker P, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact le_sup_left

private theorem truncated_kernel_to_residue_conormal
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S] (P : Extension.{u} R S) [IsLocalRing P.Ring] (N : ℕ)
    (hAR : ((IsLocalRing.maximalIdeal P.Ring) ^ N •
        (⊤ : Submodule P.Ring P.Ring) ⊓ P.ker) ≤
      (IsLocalRing.maximalIdeal P.Ring) • P.ker) :
    let f := Ideal.Quotient.factorₐ R
      (sup_le_sup (Ideal.pow_le_self (I := P.ker) (by decide : 2 ≠ 0))
        (le_refl (IsLocalRing.maximalIdeal P.Ring ^ N)))
    ∃ l : RingHom.ker f →ₗ[P.Ring]
        (P.Cotangent ⧸ (IsLocalRing.maximalIdeal S • (⊤ : Submodule S P.Cotangent))),
      ∀ (j : P.ker) (k : RingHom.ker f),
        (k : P.Ring ⧸ (P.ker ^ 2 ⊔ IsLocalRing.maximalIdeal P.Ring ^ N)) =
          Ideal.Quotient.mk _ j.val →
        l k = Submodule.Quotient.mk (Extension.Cotangent.mk j) := by
  let L := IsLocalRing.maximalIdeal P.Ring ^ N
  let I := P.ker ^ 2 ⊔ L
  let f := Ideal.Quotient.factorₐ R
    (sup_le_sup (Ideal.pow_le_self (I := P.ker) (by decide : 2 ≠ 0)) (le_refl L))
  let p : Submodule S P.Cotangent := IsLocalRing.maximalIdeal S • ⊤
  let q : P.ker →ₗ[P.Ring] (P.Cotangent ⧸ p) :=
    (p.mkQ.restrictScalars P.Ring).comp Extension.Cotangent.mk
  let t : P.ker →ₗ[P.Ring] RingHom.ker f :=
    (((Ideal.Quotient.mkₐ P.Ring I).toLinearMap).comp P.ker.subtype).codRestrict
      ((RingHom.ker f).restrictScalars P.Ring) (by
        intro j
        change f (Ideal.Quotient.mk I j.val) = 0
        rw [Ideal.Quotient.factorₐ_apply_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact (show P.ker ≤ P.ker ⊔ L from le_sup_left) j.2)
  have ht : Function.Surjective t := by
    intro k
    have hk : k.val ∈ P.ker.map (Ideal.Quotient.mk I) := by
      simpa only [f, I, truncated_factor_ker P] using k.2
    obtain ⟨j, hj, he⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective).mp hk
    exact ⟨⟨j, hj⟩, Subtype.ext he⟩
  have hq : LinearMap.ker t ≤ LinearMap.ker q := by
    intro j hj
    have hji : j.val ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact congrArg Subtype.val hj
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hji
    have haJ : a ∈ P.ker := (Ideal.pow_le_self (I := P.ker)
      (by decide : 2 ≠ 0)) ha
    have hbJ : b ∈ P.ker := by
      have : b = j.val - a := by rw [← hab]; simp
      rw [this]
      exact P.ker.sub_mem j.2 haJ
    have hbAR : b ∈ IsLocalRing.maximalIdeal P.Ring • P.ker := by
      apply hAR
      constructor
      · change b ∈ ((IsLocalRing.maximalIdeal P.Ring ^ N) * ⊤ : Ideal P.Ring)
        simpa only [Ideal.mul_top] using hb
      · exact hbJ
    have hkill : IsLocalRing.maximalIdeal P.Ring •
        (⊤ : Submodule P.Ring P.ker) ≤ LinearMap.ker q := by
      let := IsLocalHom.of_surjective (algebraMap P.Ring S) P.algebraMap_surjective
      intro y hy
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro r hr z _
        rw [LinearMap.mem_ker, q.map_smul]
        change p.mkQ (r • Extension.Cotangent.mk z) = 0
        apply (Submodule.Quotient.mk_eq_zero p).mpr
        rw [← algebraMap_smul S r]
        apply Submodule.smul_mem_smul ?_ (Submodule.mem_top)
        change r ∈ (IsLocalRing.maximalIdeal S).comap (algebraMap P.Ring S)
        rwa [IsLocalRing.maximalIdeal_comap]
      · intro x y hx hy
        exact (LinearMap.ker q).add_mem hx hy
    have hqb : q ⟨b, hbJ⟩ = 0 := hkill
      ((Submodule.mem_smul_top_iff _ _ ⟨b, hbJ⟩).mpr hbAR)
    have hqa : q ⟨a, haJ⟩ = 0 := by
      change p.mkQ (Extension.Cotangent.mk ⟨a, haJ⟩) = 0
      rw [(Extension.Cotangent.mk_eq_zero_iff _).mpr ha, map_zero]
    have hjab : j = ⟨a, haJ⟩ + ⟨b, hbJ⟩ := Subtype.ext hab.symm
    rw [LinearMap.mem_ker, hjab, q.map_add, hqa, hqb, add_zero]
  let e := t.quotKerEquivOfSurjective ht
  refine ⟨((LinearMap.ker t).liftQ q hq).comp e.symm.toLinearMap, ?_⟩
  intro j k hk
  have htk : t j = k := Subtype.ext hk.symm
  subst k
  change ((LinearMap.ker t).liftQ q hq) (e.symm (t j)) = q j
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- A section at a truncation satisfying the Artin--Rees bound detects the residue kernel:
the preimage under the cotangent complex of `𝔪_S • P.CotangentSpace` lies in `𝔪_S • P.Cotangent`.
-/
theorem truncated_section_conormal_residue_kernel_comap
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S] (P : Extension.{u} R S) [IsLocalRing P.Ring]
    (N : ℕ) (hN : 2 ≤ N)
    (hAR : ((IsLocalRing.maximalIdeal P.Ring) ^ N •
        (⊤ : Submodule P.Ring P.Ring) ⊓ P.ker) ≤
      (IsLocalRing.maximalIdeal P.Ring) • P.ker)
    (σ : (P.Ring ⧸ (P.ker ⊔ IsLocalRing.maximalIdeal P.Ring ^ N)) →ₐ[R]
        (P.Ring ⧸ (P.ker ^ 2 ⊔ IsLocalRing.maximalIdeal P.Ring ^ N)))
    (hσ : (Ideal.Quotient.factorₐ R
        (sup_le_sup (Ideal.pow_le_self (by decide : 2 ≠ 0)) le_rfl)).comp σ =
      AlgHom.id R _) :
    Submodule.comap P.cotangentComplex
      ((IsLocalRing.maximalIdeal S) • (⊤ : Submodule S P.CotangentSpace)) ≤
      (IsLocalRing.maximalIdeal S) • (⊤ : Submodule S P.Cotangent) := by
  have _hN := hN
  let L := IsLocalRing.maximalIdeal P.Ring ^ N
  let f := Ideal.Quotient.factorₐ R
    (sup_le_sup (Ideal.pow_le_self (I := P.ker) (by decide : 2 ≠ 0)) (le_refl L))
  let p : Submodule S P.Cotangent := IsLocalRing.maximalIdeal S • ⊤
  obtain ⟨l, hl⟩ := truncated_kernel_to_residue_conormal P N hAR
  let d₀ := derivationOfSectionOfKerSqZero f (truncated_factor_ker_sq P P.ker L) σ hσ
  let d := l.compDer (d₀.compAlgebraMap P.Ring)
  let v : P.CotangentSpace →ₗ[S] (P.Cotangent ⧸ p) :=
    d.liftKaehlerDifferential.liftBaseChange S
  have hv : v.comp P.cotangentComplex = p.mkQ := by
    apply LinearMap.ext
    intro x
    obtain ⟨j, rfl⟩ := Extension.Cotangent.mk_surjective x
    rw [LinearMap.comp_apply, Extension.cotangentComplex_mk]
    dsimp only [v]
    rw [LinearMap.liftBaseChange_tmul, one_smul,
      Derivation.liftKaehlerDifferential_comp_D]
    apply hl j
    change Ideal.Quotient.mk _ j.val - σ (f (Ideal.Quotient.mk _ j.val)) = _
    rw [Ideal.Quotient.factorₐ_apply_mk]
    have hj : Ideal.Quotient.mk (P.ker ⊔ L) j.val = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ((show P.ker ≤ P.ker ⊔ L from le_sup_left) j.2)
    rw [hj, map_zero, sub_zero]
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero p).mp
  have hkill : IsLocalRing.maximalIdeal S • (⊤ : Submodule S P.CotangentSpace) ≤
      LinearMap.ker v := by
    intro y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro r hr z _
      rw [LinearMap.mem_ker, v.map_smul]
      obtain ⟨a, ha⟩ := p.mkQ_surjective (v z)
      rw [← ha, ← p.mkQ.map_smul]
      exact (Submodule.Quotient.mk_eq_zero p).mpr
        (Submodule.smul_mem_smul hr Submodule.mem_top)
    · intro a b ha hb
      exact (LinearMap.ker v).add_mem ha hb
  simpa only [LinearMap.comp_apply, Submodule.mkQ_apply] using
    (LinearMap.congr_fun hv x).symm.trans (hkill hx)


/-- Let `P` be a local presentation of a local `R`-algebra `S` whose kernel satisfies the
Artin--Rees bound at `N ≥ 2`, and let `σ` be an `R`-algebra section of the truncation
`P.Ring/(ker² + 𝔪^N) → P.Ring/(ker + 𝔪^N)`. If the image of `x : P.Cotangent` in the cotangent
space lies in `𝔪_S` times it, then `x` lies in `𝔪_S • P.Cotangent`. -/
theorem truncated_section_conormal_residue_kernel
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S] (P : Extension.{u} R S) [IsLocalRing P.Ring]
    (N : ℕ) (hN : 2 ≤ N)
    (hAR : ((IsLocalRing.maximalIdeal P.Ring) ^ N •
        (⊤ : Submodule P.Ring P.Ring) ⊓ P.ker) ≤
      (IsLocalRing.maximalIdeal P.Ring) • P.ker)
    (σ : (P.Ring ⧸ (P.ker ⊔ IsLocalRing.maximalIdeal P.Ring ^ N)) →ₐ[R]
        (P.Ring ⧸ (P.ker ^ 2 ⊔ IsLocalRing.maximalIdeal P.Ring ^ N)))
    (hσ : (Ideal.Quotient.factorₐ R
        (sup_le_sup (Ideal.pow_le_self (by decide : 2 ≠ 0)) le_rfl)).comp σ =
      AlgHom.id R _) :
    ∀ x : P.Cotangent,
      P.cotangentComplex x ∈
          (IsLocalRing.maximalIdeal S) • (⊤ : Submodule S P.CotangentSpace) →
        x ∈ (IsLocalRing.maximalIdeal S) • (⊤ : Submodule S P.Cotangent) := by
  intro x hx
  exact truncated_section_conormal_residue_kernel_comap P N hN hAR σ hσ hx


end Algebra
