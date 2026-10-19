/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.Integral
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Sheaf.FieldTheory.FiniteDVRInertiaOrderPrimePart

/-!
# Finite DVR normalization and its tame inertia character

Source: Stacks Project, More on Algebra, Tags 09E8 and 09EE,
`literature/stacks-project/more-algebra.tex`, Remark `remark-finite-separable-extension`
and Lemma `lemma-galois-inertia`, equation `equation-inertia-character`.
(blueprint: lem-exc-finite-dvr-tame-inertia)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped Pointwise

namespace IsDiscreteValuationRing

private noncomputable def localAut {R G : Type*} [CommRing R] [Group G] [MulSemiringAction G R]
    (P : Ideal R) [P.IsPrime] :
    MulAction.stabilizer G P →* (Localization.AtPrime P ≃+* Localization.AtPrime P) := by
  let hmap (g : MulAction.stabilizer G P) :
      P.primeCompl.map (MulSemiringAction.toRingAut G R g).toMonoidHom = P.primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change g.1 • y ∉ P
      have hg : (g : G) • P = P := g.property
      simpa only [hg] using
        ((Ideal.smul_mem_pointwise_smul_iff).not.mpr hy : (g : G) • y ∉ (g : G) • P)
    · intro hx
      refine ⟨g.1⁻¹ • x, ?_, by simp⟩
      change g.1⁻¹ • x ∉ P
      have hg : (g : G)⁻¹ • P = P := (g⁻¹).property
      simpa only [hg] using
        ((Ideal.smul_mem_pointwise_smul_iff).not.mpr hx : (g : G)⁻¹ • x ∉ (g : G)⁻¹ • P)
  refine
    { toFun := fun g ↦ IsLocalization.ringEquivOfRingEquiv _ _
        (MulSemiringAction.toRingAut G R g) (hmap g)
      map_one' := ?_
      map_mul' := ?_ }
  · apply RingEquiv.toRingHom_injective
    apply IsLocalization.ringHom_ext P.primeCompl
    ext x
    simp
  · intro g h
    apply RingEquiv.toRingHom_injective
    apply IsLocalization.ringHom_ext P.primeCompl
    ext x
    simp

private theorem localAut_map {R G : Type*} [CommRing R] [Group G] [MulSemiringAction G R]
    (P : Ideal R) [P.IsPrime] (g : MulAction.stabilizer G P) (x : R) :
    localAut P g (algebraMap R (Localization.AtPrime P) x) =
      algebraMap R (Localization.AtPrime P) (g • x) := by
  dsimp only [localAut, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [IsLocalization.ringEquivOfRingEquiv_eq]
  rfl

private theorem uniformizer_character
    {C G : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Group G]
    (α : G →* (C ≃+* C)) (I : Subgroup G) [I.Normal]
    (hres : ∀ (g : I) (c : C), IsLocalRing.residue C (α g c) = IsLocalRing.residue C c)
    (x : C) (hx : ∀ g : I, α g x = x)
    (t : C) (ht : Irreducible t) (e : ℕ) (u : Cˣ) (hu : x = (u : C) * t ^ e) :
    ∃ χ : I →* rootsOfUnity e (IsLocalRing.ResidueField C),
      (∀ (s : C), Irreducible s → ∀ g : I, ∃ a : Cˣ,
        α g s = (a : C) * s ∧
          ((χ g : (IsLocalRing.ResidueField C)ˣ) : IsLocalRing.ResidueField C) =
            IsLocalRing.residue C (a : C)) ∧
      (χ.ker.map I.subtype).Normal := by
  classical
  let r := IsLocalRing.residue C
  have hratio : ∀ (s : C), Irreducible s → ∀ g : G,
      ∃ a : Cˣ, α g s = (a : C) * s := by
    intro s hs g
    obtain ⟨a, ha⟩ := associated_of_irreducible C hs (hs.map (α g).toMulEquiv)
    exact ⟨a, by simpa [mul_comm] using ha.symm⟩
  choose a ha using hratio t ht
  have hpow (g : I) : r (a g : C) ^ e = 1 := by
    have hh : (u : C) = α g (u : C) * (a g : C) ^ e := by
      apply mul_right_cancel₀ (pow_ne_zero e ht.ne_zero)
      calc
        (u : C) * t ^ e = x := hu.symm
        _ = α g x := (hx g).symm
        _ = α g (u : C) * (a g : C) ^ e * t ^ e := by
          rw [hu, map_mul, map_pow, ha, mul_pow, mul_assoc]
    have hh' := congrArg r hh
    rw [map_mul, hres] at hh'
    exact (mul_left_cancel₀ (u.isUnit.map r).ne_zero
      (show r (u : C) * r (a g : C) ^ e = r (u : C) * 1 by
        simpa [map_pow] using hh'.symm))
  let χ : I →* rootsOfUnity e (IsLocalRing.ResidueField C) :=
    { toFun := fun g ↦ ⟨Units.map r.toMonoidHom (a g), by
        apply (mem_rootsOfUnity e _).mpr
        apply Units.ext
        exact hpow g⟩
      map_one' := by
        apply Subtype.ext
        apply Units.ext
        change r (a (1 : I) : C) = 1
        have hh : (a (1 : G) : C) = 1 := by
          apply mul_right_cancel₀ ht.ne_zero
          simpa using (ha 1).symm
        simp [hh]
      map_mul' := by
        intro g h
        apply Subtype.ext
        apply Units.ext
        change r (a (g * h : I) : C) = r (a g : C) * r (a h : C)
        have hh : (a (g * h : I) : C) = α g (a h : C) * (a g : C) := by
          apply mul_right_cancel₀ ht.ne_zero
          rw [← ha, Subgroup.coe_mul, map_mul]
          change α g (α h t) = _
          rw [ha, map_mul, ha, mul_assoc]
        rw [hh, map_mul, hres, mul_comm] }
  have hformula : ∀ (s : C), Irreducible s → ∀ g : I, ∃ b : Cˣ,
      α g s = (b : C) * s ∧ ((χ g : (IsLocalRing.ResidueField C)ˣ) :
        IsLocalRing.ResidueField C) = r (b : C) := by
    intro s hs g
    obtain ⟨w, hw⟩ := associated_of_irreducible C ht hs
    obtain ⟨b, hb⟩ := hratio s hs g
    refine ⟨b, hb, ?_⟩
    have heq : (b : C) * (w : C) = α g (w : C) * (a g : C) := by
      apply mul_right_cancel₀ ht.ne_zero
      calc
        (b : C) * (w : C) * t = (b : C) * s := by rw [mul_assoc, mul_comm (w : C), hw]
        _ = α g s := hb.symm
        _ = α g (w : C) * (a g : C) * t := by
          rw [← hw, map_mul, ha]
          ring
    have hh := congrArg r heq
    change r (b : C) * r (w : C) = r (α g (w : C)) * r (a g : C) at hh
    rw [hres] at hh
    change r (a g : C) = r (b : C)
    exact mul_right_cancel₀ (w.isUnit.map r).ne_zero
      (by simpa only [mul_comm] using hh.symm)
  refine ⟨χ, hformula, ?_⟩
  constructor
  intro g hg δ
  obtain ⟨σ, hσ, rfl⟩ := hg
  have hσχ : χ σ = 1 := hσ
  have hconj : δ * (σ : G) * δ⁻¹ ∈ I := (inferInstance : I.Normal).conj_mem σ σ.property δ
  let τ : I := ⟨δ * (σ : G) * δ⁻¹, hconj⟩
  obtain ⟨b, hb, hχb⟩ := hformula (α δ⁻¹ t) (ht.map (α δ⁻¹).toMulEquiv) σ
  obtain ⟨c, hc, hχc⟩ := hformula t ht τ
  have hb1 : r (b : C) = 1 := by simpa [hσχ] using hχb.symm
  have hcα : (c : C) = α δ (b : C) := by
    apply mul_right_cancel₀ ht.ne_zero
    rw [← hc]
    change α (δ * (σ : G) * δ⁻¹) t = _
    rw [map_mul, map_mul]
    change α δ (α σ (α δ⁻¹ t)) = _
    rw [hb, map_mul]
    have hinv : α δ (α δ⁻¹ t) = t := by
      change (α δ * α δ⁻¹) t = t
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [hinv]
  have hc1 : r (c : C) = 1 := by
    rw [hcα]
    change IsLocalRing.residue C (α δ (b : C)) = 1
    change IsLocalRing.residue C (b : C) = 1 at hb1
    have hh := congrArg (IsLocalRing.ResidueField.mapEquiv (α δ)) hb1
    simpa using hh
  refine ⟨τ, ?_, rfl⟩
  apply Subtype.ext
  apply Units.ext
  exact hχc.trans hc1

private theorem wild_order_dvd
    {C E G : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Field E] [Group G] (r : C →+* E) (p : ℕ) [CharP E p]
    (α : G →* (C ≃+* C)) (hα : Function.Injective α)
    (t : C) (ht : Irreducible t)
    (hres : ∀ (g : G) (c : C), r (α g c) = r c)
    (hratio : ∀ g : G, ∃ a : Cˣ, α g t = (a : C) * t ∧ r (a : C) = 1)
    (g : G) (hg : g ≠ 1) : p ∣ orderOf g := by
  classical
  have hmove : ∃ c : C, α g c ≠ c := by
    by_contra! h
    apply hg
    apply hα
    ext c
    simpa using h c
  obtain ⟨c, hc⟩ := hmove
  obtain ⟨i, a, ha⟩ := eq_unit_mul_pow_irreducible (sub_ne_zero.mpr hc) ht
  choose b hb hbr using hratio
  have hsum : ∑ j ∈ Finset.range (orderOf g), α (g ^ j) (α g c - c) = 0 := by
    have hstep : ∀ j : ℕ, α (g ^ j) (α g c - c) =
        α (g ^ (j + 1)) c - α (g ^ j) c := by
      intro j
      rw [map_sub, pow_succ, map_mul]
      rfl
    simp_rw [hstep]
    rw [Finset.sum_range_sub (fun j ↦ α (g ^ j) c)]
    simp
  have hcoef : ∑ j ∈ Finset.range (orderOf g),
      (b (g ^ j) : C) ^ i * α (g ^ j) (a : C) = 0 := by
    apply (mul_eq_zero.mp (show t ^ i *
      (∑ j ∈ Finset.range (orderOf g), (b (g ^ j) : C) ^ i *
        α (g ^ j) (a : C)) = 0 from ?_)).resolve_left (pow_ne_zero _ ht.ne_zero)
    rw [Finset.mul_sum]
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [ha, RingEquiv.map_mul, RingEquiv.map_pow, hb, mul_pow]
    ring
  have hcast : (orderOf g : E) * r (a : C) = 0 := by
    have h := congrArg r hcoef
    simp only [map_sum, map_mul, map_pow, hbr, one_pow, one_mul, map_zero] at h
    simp_rw [← map_pow α, hres] at h
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h
  exact (CharP.cast_eq_zero_iff E p _).mp
    ((mul_eq_zero.mp hcast).resolve_right (a.isUnit.map r).ne_zero)

private theorem wild_card_pow
    {C G : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField C) p]
    (α : G →* (C ≃+* C)) (hα : Function.Injective α)
    (t : C) (ht : Irreducible t)
    (hres : ∀ (g : G) (c : C), IsLocalRing.residue C (α g c) = IsLocalRing.residue C c)
    (hratio : ∀ g : G, ∃ a : Cˣ, α g t = (a : C) * t ∧
      IsLocalRing.residue C (a : C) = 1) : ∃ a : ℕ, Nat.card G = p ^ a := by
  apply IsPGroup.exists_card_eq
  apply (isPGroup_iff_primeFactors_card_subset (Fact.out : p.Prime).ne_zero).mpr
  intro q hq
  obtain ⟨hqprime, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q (hp := ⟨hqprime⟩) hqdvd
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg
    exact hqprime.ne_one hg.symm
  have hdiv := wild_order_dvd (IsLocalRing.residue C) p α hα t ht hres hratio g hg1
  rw [hg] at hdiv
  have hqp : q = p := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hqprime).mp hdiv |>.symm
  simpa [hqp] using (Nat.mem_primeFactors.mpr
    ⟨Fact.out, dvd_refl p, (Fact.out : p.Prime).ne_zero⟩ : p ∈ p.primeFactors)

private theorem tame_cardinality
    {G E : Type*} [Group G] [Finite G] [Field E]
    (p e : ℕ) [Fact p.Prime] [CharP E p] (he : 0 < e)
    (χ : G →* rootsOfUnity e E)
    (hG : ∃ b : ℕ, Nat.card G = (e / p ^ e.factorization p) * p ^ b)
    (hker : ∃ a : ℕ, Nat.card χ.ker = p ^ a) :
    rootsOfUnity e E = rootsOfUnity (e / p ^ e.factorization p) E ∧
      IsCyclic (rootsOfUnity (e / p ^ e.factorization p) E) ∧
      Nat.card (rootsOfUnity (e / p ^ e.factorization p) E) =
        e / p ^ e.factorization p ∧
      ∃ θ : (G ⧸ χ.ker) ≃* rootsOfUnity (e / p ^ e.factorization p) E,
        ∀ σ : G, (θ (QuotientGroup.mk σ) : Eˣ) = (χ σ : Eˣ) := by
  classical
  let n := e / p ^ e.factorization p
  have hp : p.Prime := Fact.out
  have hn : 0 < n := Nat.ordCompl_pos p he.ne'
  have : NeZero e := ⟨he.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  have hroots : rootsOfUnity e E = rootsOfUnity n E := by
    ext z
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self e p]
    exact mem_rootsOfUnity_prime_pow_mul_iff E p (e.factorization p) n
  have hncard : Nat.card (rootsOfUnity e E) ∣ n := by
    obtain ⟨z, hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := rootsOfUnity e E)
    rw [← hz]
    apply orderOf_dvd_iff_pow_eq_one.mpr
    apply Subtype.ext
    change (z : Eˣ) ^ n = 1
    exact (mem_rootsOfUnity n (z : Eˣ)).mp (hroots ▸ z.property)
  have hr_dvd : Nat.card χ.range ∣ n :=
    (Subgroup.card_subgroup_dvd_card χ.range).trans hncard
  have hpn : ¬ p ∣ n := Nat.not_dvd_ordCompl hp he.ne'
  have hpr : ¬ p ∣ Nat.card χ.range := fun h => hpn (h.trans hr_dvd)
  have hcount : Nat.card χ.ker * Nat.card χ.range = Nat.card G := by
    rw [← Subgroup.index_ker χ]
    exact χ.ker.card_mul_index
  obtain ⟨a, ha⟩ := hker
  obtain ⟨b, hb⟩ := hG
  rw [ha, hb, Nat.mul_comm n] at hcount
  have hr : Nat.card χ.range = n := by
    have h := congrArg (fun m : ℕ => m / p ^ m.factorization p) hcount
    simpa only [Nat.ordCompl_pow_mul_of_not_dvd a hp hpr,
      Nat.ordCompl_pow_mul_of_not_dvd b hp hpn] using h
  have hbound : Nat.card (rootsOfUnity e E) ≤ n := by
    rw [Nat.card_congr (MulEquiv.subgroupCongr hroots).toEquiv]
    exact card_rootsOfUnity E n
  have hsurj : Function.Surjective χ := by
    have hinc : Function.Surjective ((↑) : χ.range → rootsOfUnity e E) :=
      (Subtype.val_injective.bijective_of_nat_card_le (hr ▸ hbound)).2
    intro z
    obtain ⟨⟨_, σ, hσ⟩, hz⟩ := hinc z
    exact ⟨σ, hσ.trans hz⟩
  refine ⟨hroots, inferInstance, ?_, ?_⟩
  · have hc : Nat.card (rootsOfUnity e E) = n :=
      hbound.antisymm (hr ▸ Nat.card_le_card_of_injective
        ((↑) : χ.range → rootsOfUnity e E) Subtype.val_injective)
    exact (Nat.card_congr (MulEquiv.subgroupCongr hroots).toEquiv).symm.trans hc
  · refine ⟨(QuotientGroup.quotientKerEquivOfSurjective χ hsurj).trans
      (MulEquiv.subgroupCongr hroots), ?_⟩
    intro σ
    rfl


set_option maxHeartbeats 800000 in
-- The normalization and localization instance chains require more elaboration heartbeats.
/-- Finite normalization of a DVR and the tame inertia character at every maximal ideal.
The maps `j` and `ρ` are characterized on the original rings: `j` extends the inclusion
of the integral closure in `L`, and `ρ` is the induced residue-field embedding.
The integer `e` is the normalized additive valuation of every base uniformizer.
The character formula is required for every local uniformizer, expressing independence
of that choice. Its kernel, mapped into the decomposition group, is normal there.
The final equivalence agrees with the character on every quotient representative.

Source: Stacks Project, More on Algebra, Tags 09E8 and 09EE, Remark
`remark-finite-separable-extension`, Lemma `lemma-galois-inertia`, and equation
`equation-inertia-character`; Fields, Tag 09HW for roots of unity.
(blueprint: lem-exc-finite-dvr-tame-inertia)

Proof:
1. A DVR is a PID (`def-sc-discrete-valuation-ring`), hence Noetherian and normal
   (`lem-weil-pbc-pid-noetherian-normal`), and has dimension one
   (`lem-sc-dvr-dimension-one`). Finite separability gives finite normalization
   (`lem-weil-pbc-noetherian-normal-separable-integral-closure-finite`).
2. The normalization is Dedekind with finite residue extensions by
   `lem-sc-integral-closure-dedekind-surjective-fibres`; its maximal localizations
   are DVRs by `lem-sc-dedekind-localization-dvr`. Its fraction field is L by
   `lem-weil-pbc-integral-closure-finite-extension-normal`, and localization does
   not change that field. Localizing and then taking the residue field gives
   precisely the prime's residue field (`def-weil-pbc-localization-at-prime`).
3. The contraction of the maximal ideal is maximal: a field integral over a
   subdomain forces that subdomain to be a field, since a monic equation for
   the inverse of a nonzero element expresses the inverse in the subdomain.
   Thus the contraction is the maximal ideal of A. The local map gives e > 0
   and π_A = u t^e. Automorphisms preserve integral elements and those fixing
   the ideal extend to fractions b/s by σ(b)/σ(s). The inertia group is the
   kernel of the residue action of its stabilizer and is normal there.
4. Apply `lem-exc-dvr-inertia-order-prime-part`: if n is the prime-to-p part of e,
   then |I| = n p^b. This allows inseparable residue extensions; |I| = e is
   not assumed.
5. Write σ(t) = a_σ t with a_σ a unit. Applying σ to π_A = u t^e gives
   u = σ(u) a_σ^e. Inertia acts trivially on residues, so the residue of a_σ
   is an e-th root. The identity a_(στ) = σ(a_τ) a_σ proves multiplicativity.
   For t' = z t the ratio changes by σ(z)/z, whose residue is one, so the
   same character satisfies the formula for every uniformizer.
6. If δ is in the stabilizer and σ is in the kernel, use the uniformizer
   t' = δ⁻¹(t). The residue of (δσδ⁻¹)(t)/t is the residue action of δ
   applied to the character of σ computed with t', and hence is one.
   This proves normality of the kernel in the decomposition group.
7. For σ in the kernel, (σ - 1)(t^i C) is contained in t^(i+1) C, by reducing
   σ(t)/t and σ(a) for t^i a. For σ ≠ 1 of order m choose c not fixed by σ
   (otherwise σ fixes Frac(C) = L). Write d = σ(c) - c = t^i a with a a unit
   and finite i ≥ 1. Then σ^j(d) ≡ d modulo t^(i+1) for every j. Telescoping
   σ^m(c) - c gives m d ≡ 0 modulo t^(i+1). Divide by t^i and reduce:
   m times the nonzero residue of a is zero, so p divides m.
8. The kernel is finite. Cauchy's theorem (`lem-exc-finite-group-cauchy`)
   supplies an element of order q for every prime divisor q of its order.
   Step 7 forces q = p. Prime factorization gives order p^a, including a = 0.
9. Write e = n p^s. In characteristic p the binomial coefficients between
   the endpoints vanish, so (X^n - 1)^(p^s) = X^e - 1. In a field a power
   vanishes only when its base does; therefore μ_e = μ_n. By
   `lem-exc-field-roots-cyclic-bound`, μ_n is finite cyclic of order at most n.
   The order of a generator divides n, hence the image order divides n and
   is prime to p.
10. Every character fibre is a coset of its kernel. Thus |I| = |P| |im χ|.
    Compare with Steps 4 and 8 and take prime-to-p parts to obtain |im χ| = n.
    The image lies in μ_n, whose order is at most n, so it is all of μ_n and
    that group has order n. The map σP ↦ χ(σ) is well-defined and surjective;
    equality of values says the quotient of the representatives lies in P,
    proving injectivity and giving the asserted induced isomorphism. -/
theorem finite_normalization_tame_inertia
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] :
    Module.Finite A (integralClosure A L) ∧
      ∀ (𝔫 : Ideal (integralClosure A L)) [𝔫.IsMaximal],
        ∃ hC : IsDiscreteValuationRing (Localization.AtPrime 𝔫),
          ∃ j : Localization.AtPrime 𝔫 →+* L,
            (∀ b : integralClosure A L,
              j (algebraMap (integralClosure A L) (Localization.AtPrime 𝔫) b) = (b : L)) ∧
            @IsFractionRing (Localization.AtPrime 𝔫) _ L _ j.toAlgebra ∧
            ∃ ρ : IsLocalRing.ResidueField A →+* 𝔫.ResidueField,
              (∀ a : A, ρ (IsLocalRing.residue A a) = algebraMap A 𝔫.ResidueField a) ∧
              @Module.Finite (IsLocalRing.ResidueField A) 𝔫.ResidueField _ _
                ρ.toAlgebra.toModule ∧
              ∃ e : ℕ,
                (∀ π : A, Irreducible π →
                  @addVal (Localization.AtPrime 𝔫) _ _ hC
                    (algebraMap A (Localization.AtPrime 𝔫) π) = (e : ℕ∞)) ∧
                ∃ χ : 𝔫.inertia (MulAction.stabilizer Gal(L/K) 𝔫) →*
                    rootsOfUnity e 𝔫.ResidueField,
                  (∀ (t : Localization.AtPrime 𝔫), Irreducible t →
                    ∀ σ : 𝔫.inertia (MulAction.stabilizer Gal(L/K) 𝔫),
                      ∃ a : (Localization.AtPrime 𝔫)ˣ,
                        j (a : Localization.AtPrime 𝔫) = σ.1.1 (j t) / j t ∧
                        ((χ σ : 𝔫.ResidueFieldˣ) : 𝔫.ResidueField) =
                          IsLocalRing.residue (Localization.AtPrime 𝔫) a) ∧
                  (χ.ker.map (𝔫.inertia (MulAction.stabilizer Gal(L/K) 𝔫)).subtype).Normal ∧
                  Finite χ.ker ∧ (∃ a : ℕ, Nat.card χ.ker = p ^ a) ∧
                  rootsOfUnity e 𝔫.ResidueField =
                    rootsOfUnity (e / p ^ e.factorization p) 𝔫.ResidueField ∧
                  IsCyclic (rootsOfUnity (e / p ^ e.factorization p) 𝔫.ResidueField) ∧
                  Nat.card (rootsOfUnity (e / p ^ e.factorization p) 𝔫.ResidueField) =
                    e / p ^ e.factorization p ∧
                  ∃ θ : (𝔫.inertia (MulAction.stabilizer Gal(L/K) 𝔫) ⧸ χ.ker) ≃*
                      rootsOfUnity (e / p ^ e.factorization p) 𝔫.ResidueField,
                    ∀ σ : 𝔫.inertia (MulAction.stabilizer Gal(L/K) 𝔫),
                      (θ (QuotientGroup.mk σ) : 𝔫.ResidueFieldˣ) = (χ σ : 𝔫.ResidueFieldˣ) := by
  classical
  let B := integralClosure A L
  have hfin : Module.Finite A B := IsIntegralClosure.finite A K L B
  have hDed : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K L B
  have hFrac : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  refine ⟨hfin, ?_⟩
  intro 𝔫 h𝔫
  have hq : (𝔫.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔫
  have hqeq : 𝔫.comap (algebraMap A B) = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal hq
  have hinj : Function.Injective (algebraMap A B) := by
    apply Function.Injective.of_comp (f := algebraMap B L)
    change Function.Injective ((algebraMap B L).comp (algebraMap A B))
    rw [← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have hn0 : 𝔫 ≠ ⊥ := by
    intro hn
    rw [hn, Ideal.comap_bot_of_injective _ hinj] at hqeq
    exact IsDiscreteValuationRing.not_a_field A hqeq.symm
  let C := Localization.AtPrime 𝔫
  have hC : IsDiscreteValuationRing C :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hn0 C
  let j : C →+* L := IsLocalization.lift (S := C)
    (fun y : 𝔫.primeCompl => IsUnit.mk0 (algebraMap B L y)
      (map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective B L)
        (𝔫.primeCompl_le_nonZeroDivisors y.property)))
  have hj : ∀ b : B, j (algebraMap B C b) = (b : L) :=
    IsLocalization.lift_eq _
  let : Algebra C L := j.toAlgebra
  have : IsScalarTower B C L := IsScalarTower.of_algebraMap_eq' (by
    ext b
    exact (hj b).symm)
  have hCL : IsFractionRing C L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔫.primeCompl C L
  refine ⟨hC, j, hj, hCL, ?_⟩
  have : IsLocalHom (algebraMap A 𝔫.ResidueField) := by
    constructor
    intro a ha
    by_contra ham
    have hab : algebraMap A B a ∈ 𝔫 := by
      change a ∈ 𝔫.comap (algebraMap A B)
      rw [hqeq]
      exact ham
    have haz : algebraMap A 𝔫.ResidueField a = 0 := by
      rw [IsScalarTower.algebraMap_apply A B 𝔫.ResidueField]
      exact Ideal.algebraMap_residueField_eq_zero.mpr hab
    exact (isUnit_iff_ne_zero.mp ha) haz
  let ρ := IsLocalRing.ResidueField.lift (algebraMap A 𝔫.ResidueField)
  have hρ : ∀ a : A, ρ (IsLocalRing.residue A a) = algebraMap A 𝔫.ResidueField a :=
    fun _ => rfl
  let rhoAlg : Algebra (IsLocalRing.ResidueField A) 𝔫.ResidueField := ρ.toAlgebra
  have : IsScalarTower A (IsLocalRing.ResidueField A) 𝔫.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (by ext a; exact (hρ a).symm)
  have : Module.Finite A 𝔫.ResidueField := Module.Finite.trans B 𝔫.ResidueField
  let rhoMod : Module (IsLocalRing.ResidueField A) 𝔫.ResidueField := rhoAlg.toModule
  have hρfin : Module.Finite (IsLocalRing.ResidueField A) 𝔫.ResidueField :=
    Module.Finite.of_restrictScalars_finite A _ _
  refine ⟨ρ, hρ, hρfin, ?_⟩
  have hlocal : IsLocalHom (algebraMap A C) := by
    apply ((IsLocalRing.local_hom_TFAE _).out 3 0).mp
    intro a ha
    change algebraMap A C a ∈ IsLocalRing.maximalIdeal C
    rw [IsScalarTower.algebraMap_apply A B C]
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff C 𝔫 _).mpr
    change a ∈ 𝔫.comap (algebraMap A B)
    rwa [hqeq]
  obtain ⟨πA, hπA⟩ := exists_irreducible A
  obtain ⟨t, ht⟩ := exists_irreducible C
  have hπ0 : algebraMap A C πA ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A B C]
    simpa only [map_zero] using
      (IsLocalization.injective C 𝔫.primeCompl_le_nonZeroDivisors).ne
        (hinj.ne hπA.ne_zero)
  obtain ⟨e, u, hu⟩ := eq_unit_mul_pow_irreducible hπ0 ht
  have he : 0 < e := by
    by_contra hh
    have he0 : e = 0 := Nat.eq_zero_of_not_pos hh
    have hunit : IsUnit (algebraMap A C πA) := by simp [hu, he0]
    exact hπA.not_isUnit (isUnit_of_map_unit (algebraMap A C) πA hunit)
  have hval : ∀ π : A, Irreducible π →
      addVal C (algebraMap A C π) = (e : ℕ∞) := by
    intro π hπ
    rw [← addVal_def (algebraMap A C πA) u ht e hu]
    apply (addVal_eq_iff_associated _ _).mpr
    exact (associated_of_irreducible A hπ hπA).map (algebraMap A C)
  refine ⟨e, hval, ?_⟩
  let n := e / p ^ e.factorization p
  have hp : p.Prime := Fact.out
  have hn : 0 < n := Nat.ordCompl_pos p he.ne'
  have hn_dvd : n ∣ e := Nat.ordCompl_dvd e p
  have hn_coprime : Nat.Coprime n p := (Nat.coprime_ordCompl hp he.ne').symm
  have hn_max : ∀ d : ℕ, d ∣ e → Nat.Coprime d p → d ≤ n := by
    intro d hd hc
    exact Nat.le_of_dvd hn (Nat.dvd_ordCompl_of_dvd_not_dvd hd
      ((hp.coprime_iff_not_dvd).mp hc.symm))
  obtain ⟨hIfin, b, hIcard⟩ := inertia_order_prime_part A K L p 𝔫 πA
    ((irreducible_iff_uniformizer πA).mp hπA) t
    ((irreducible_iff_uniformizer t).mp ht) e he u hu n hn_dvd hn_coprime hn_max
  let D := MulAction.stabilizer Gal(L/K) 𝔫
  let I := 𝔫.inertia D
  let α : D →* (C ≃+* C) := localAut 𝔫
  have hαmap (g : D) (b : B) :
      α g (algebraMap B C b) = algebraMap B C (g • b) := localAut_map 𝔫 g b
  have hαj (g : D) (c : C) : j (α g c) = g.1 (j c) := by
    have hh : j.comp (α g).toRingHom = g.1.toRingHom.comp j := by
      apply IsLocalization.ringHom_ext 𝔫.primeCompl
      ext b
      change j (α g (algebraMap B C b)) = g.1 (j (algebraMap B C b))
      rw [hαmap, hj, hj]
      rfl
    exact DFunLike.congr_fun hh c
  have hαinj : Function.Injective α := by
    intro g h hgh
    apply Subtype.ext
    apply AlgEquiv.coe_ringEquiv_injective
    apply RingEquiv.toRingHom_injective
    apply IsFractionRing.ringHom_ext (A := B)
    intro b
    change g.1 (b : L) = h.1 (b : L)
    rw [← hj b, ← hαj, ← hαj, hgh]
  have hres (g : I) (c : C) :
      IsLocalRing.residue C (α g c) = IsLocalRing.residue C c := by
    have hh : (IsLocalRing.residue C).comp (α g).toRingHom =
        IsLocalRing.residue C := by
      apply IsLocalization.ringHom_ext 𝔫.primeCompl
      ext b
      change IsLocalRing.residue C (α g (algebraMap B C b)) =
        IsLocalRing.residue C (algebraMap B C b)
      rw [hαmap]
      change algebraMap B 𝔫.ResidueField (g • b) = algebraMap B 𝔫.ResidueField b
      rw [← sub_eq_zero, ← map_sub]
      exact Ideal.algebraMap_residueField_eq_zero.mpr (g.property b)
    exact DFunLike.congr_fun hh c
  have hfix (g : I) : α g (algebraMap A C πA) = algebraMap A C πA := by
    apply IsFractionRing.injective C L
    change j (α g (algebraMap A C πA)) = j (algebraMap A C πA)
    rw [hαj]
    rw [IsScalarTower.algebraMap_apply A B C, hj]
    change g.1.1 (algebraMap A L πA) = algebraMap A L πA
    rw [IsScalarTower.algebraMap_apply A K L, AlgEquiv.commutes]
  obtain ⟨χ, hχ, hnormal⟩ := uniformizer_character α I hres _ hfix t ht e u hu
  have : Finite I := hIfin
  have : Finite χ.ker := inferInstance
  have : CharP 𝔫.ResidueField p := charP_of_injective_ringHom ρ.injective p
  let αP : χ.ker →* (C ≃+* C) := (α.comp I.subtype).comp χ.ker.subtype
  have hαP : Function.Injective αP := hαinj.comp
    (Subtype.val_injective.comp Subtype.val_injective)
  have hP_res (g : χ.ker) (c : C) :
      IsLocalRing.residue C (αP g c) = IsLocalRing.residue C c := hres g c
  have hP_ratio (g : χ.ker) : ∃ a : Cˣ, αP g t = (a : C) * t ∧
      IsLocalRing.residue C (a : C) = 1 := by
    obtain ⟨a, ha, hχα⟩ := hχ t ht g
    refine ⟨a, ha, ?_⟩
    have hg : χ g.1 = 1 := g.property
    simpa only [hg, OneMemClass.coe_one, Units.val_one] using hχα.symm
  obtain ⟨a, hcard⟩ := wild_card_pow p αP hαP t ht hP_res hP_ratio
  obtain ⟨hroots, hcyc, hrootcard, θ, hθ⟩ :=
    tame_cardinality p e he χ ⟨b, hIcard⟩ ⟨a, hcard⟩
  refine ⟨χ, ?_, hnormal, inferInstance, ⟨a, hcard⟩, hroots, hcyc, hrootcard, θ, hθ⟩
  intro s hs g
  obtain ⟨a, ha, hχa⟩ := hχ s hs g
  refine ⟨a, ?_, hχa⟩
  have hh := congrArg j ha
  rw [hαj, map_mul] at hh
  have hs0 : j s ≠ 0 := by
    change algebraMap C L s ≠ 0
    simpa only [map_zero] using (IsFractionRing.injective C L).ne hs.ne_zero
  exact (eq_div_iff hs0).mpr hh.symm

end IsDiscreteValuationRing
