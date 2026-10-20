/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.FieldTheory.TameRootsProduct
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.PGroup

import Sheaf.RingTheory.IntegralComponentHenselianPermanence
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootsOfUnity
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.CharP.Reduced

/-! Finite Galois images of the subgroup fixing the tame radical tower. -/

@[expose] public section
set_option autoImplicit false
universe u v w
namespace IsDiscreteValuationRing

private theorem units_pow_surjective
    (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R]
    (n : ℕ) (hn : 0 < n) (hnR : IsUnit (n : R)) (u : Rˣ) :
    ∃ b : Rˣ, b ^ n = u := by
  let k := IsLocalRing.ResidueField R
  have hnk : (n : k) ≠ 0 := by
    simpa using (hnR.map (IsLocalRing.residue R)).ne_zero
  let : NeZero (n : k) := ⟨hnk⟩
  obtain ⟨a₀, ha₀⟩ := IsSepClosed.exists_pow_nat_eq (k := k)
    (IsLocalRing.residue R (u : R)) n
  have ha₀ne : a₀ ≠ 0 := by
    intro h
    have : IsLocalRing.residue R (u : R) = 0 := by
      rw [← ha₀, h, zero_pow hn.ne']
    exact (u.isUnit.map (IsLocalRing.residue R)).ne_zero this
  let f : Polynomial R := Polynomial.X ^ n - Polynomial.C (u : R)
  have hf : f.Monic := Polynomial.monic_X_pow_sub_C _ hn.ne'
  have hroot : Polynomial.aeval a₀ f = 0 := by
    simp only [f, Polynomial.aeval_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [ha₀]
    change IsLocalRing.residue R (u : R) - IsLocalRing.residue R (u : R) = 0
    exact sub_self _
  have hderiv : Polynomial.aeval a₀ f.derivative ≠ 0 := by
    simpa [f, Polynomial.derivative_X_pow] using
      mul_ne_zero hnk (pow_ne_zero (n - 1) ha₀ne)
  have hensel := ((HenselianLocalRing.TFAE R).out 0 1).mp
    (inferInstance : HenselianLocalRing R)
  obtain ⟨a, ha, hres⟩ := hensel f hf a₀ hroot hderiv
  have hau : IsUnit a := (IsLocalRing.residue_ne_zero_iff_isUnit a).mp (hres ▸ ha₀ne)
  refine ⟨hau.unit, Units.ext ?_⟩
  simpa [f, Polynomial.IsRoot, sub_eq_zero] using ha

private theorem roots_fixed
    (R : Type u) [CommRing R] [IsDomain R] [IsStrictlyHenselianLocalRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (E : Type w) [Field E] [Algebra K E]
    (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : R))
    (x : E) (hx : x ^ n = 1) (h : Gal(E/K)) : h x = x := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  let g : R →+* E := (algebraMap K E).comp (algebraMap R K)
  have hg : Function.Injective g :=
    (algebraMap K E).injective.comp (IsFractionRing.injective R K)
  let f : rootsOfUnity n R →* rootsOfUnity n E := restrictRootsOfUnity g n
  have hfi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    apply hg
    exact congrArg (fun z : rootsOfUnity n E ↦ ((z : Eˣ) : E)) hab
  have hcard := (AlgebraicGeometry.Scheme.strict_local_roots_of_unity R n ⟨hn, hu⟩).1
  have hsurj : Function.Surjective f := by
    apply ((Nat.bijective_iff_injective_and_card f).mpr ⟨hfi, ?_⟩).2
    apply Nat.le_antisymm
    · exact Nat.card_le_card_of_injective f hfi
    · rw [hcard]
      exact card_rootsOfUnity E n
  obtain ⟨a, ha⟩ := hsurj (rootsOfUnity.mkOfPowEq x hx)
  have hxa : g ((a : Rˣ) : R) = x :=
    congrArg (fun z : rootsOfUnity n E ↦ ((z : Eˣ) : E)) ha
  rw [← hxa]
  exact h.commutes _

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

private theorem tame_order_isUnit
    (R : Type u) [CommRing R] [IsLocalRing R]
    (p : ℕ) (hp : p = if ringChar (IsLocalRing.ResidueField R) = 0 then 1
      else ringChar (IsLocalRing.ResidueField R)) (d : TameRoots.Order p) :
    IsUnit (d.1 : R) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  rw [map_natCast]
  change ¬(d.1 : IsLocalRing.ResidueField R) = 0
  rw [ringChar.spec]
  by_cases h : ringChar (IsLocalRing.ResidueField R) = 0
  · simpa [h] using d.2.1.ne'
  · have hp' : p = ringChar (IsLocalRing.ResidueField R) := by simpa [h] using hp
    intro hd
    have : p = 1 := Nat.eq_one_of_dvd_coprimes d.2.2 (hp' ▸ hd) dvd_rfl
    exact CharP.ringChar_ne_one (R := IsLocalRing.ResidueField R) (hp' ▸ this)


/-- The subgroup fixing all tame uniformizer radicals has a p-group image on each finite
normal subextension. For p=1 this means that image is trivial.
Source: Stacks Project, pione.tex, Tags 0BUA and 0BUB; more-algebra.tex, Tag 09EE.
(blueprint: lem-per-finite-radical-restriction).

Proof: The normalization B of R in L is finite, Dedekind and has fraction field L.
Integral connected henselian permanence makes B strictly henselian and its structure map
local, with algebraic residue extension. This makes B a DVR. Its residue field is purely
inseparable over that of R; uniqueness of embeddings makes every automorphism residue-trivial.
Write π = u w^e in B, and e = q n, where q is the p-primary part (one when p=1) and n is
prime to p. Hensel lifting extracts an n-th root b of u in B. The element β=b w^q is an
n-th root of π. Its ratio with α_n is a root of unity coming from R, so every radical-fixing
automorphism fixes β. If g(w)=a w, reducing g(β)=β and cancelling the nonzero residue of b
gives residue(a)^q=1. In positive characteristic injectivity of iterated Frobenius gives
residue(a)=1; for p=1 this is immediate. For nonidentity g, choose c moved by g and write
g(c)-c=w^i v with v a unit. Telescoping over the finite order of g, cancelling w^i and
reducing shows the residue characteristic divides orderOf g. In positive characteristic,
Cauchy's theorem forces every prime divisor of the image group order to be p, giving a
p-group. In characteristic zero the same divisibility contradicts positive finite order,
so the image is trivial. This includes the bottom field and trivial images. -/
theorem finite_radical_restriction_p_group
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsStrictlyHenselianLocalRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (Ksep : Type w) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (p : ℕ) (hp : p = if ringChar (IsLocalRing.ResidueField R) = 0 then 1
      else ringChar (IsLocalRing.ResidueField R))
    (π : R) (hπ : Irreducible π) (α : TameRoots.Order p → Ksep)
    (hα : ∀ d : TameRoots.Order p,
      α d ^ d.1 = algebraMap K Ksep (algebraMap R K π))
    (_hαc : ∀ d e : TameRoots.Order p, d.1 ∣ e.1 → α e ^ (e.1 / d.1) = α d)
    (L : IntermediateField K Ksep) [FiniteDimensional K L] [Normal K L] :
    IsPGroup p (((AlgEquiv.restrictNormalHom L).comp
      (⨅ d : TameRoots.Order p, MulAction.stabilizer Gal(Ksep/K) (α d)).subtype).range) :=
  by
  classical
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let B := integralClosure R L
  let : Module.Finite R B := IsIntegralClosure.finite R K L B
  let : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain R K L B
  let : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  obtain ⟨hB, hlocal, halg, hstrict⟩ :=
    HenselianLocalRing.integral_component_henselian_permanence R B (by
      intro e he
      have hz : e * (e - 1) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
      exact (mul_eq_zero.mp hz).imp_right sub_eq_zero.mp)
  let := hB
  let := hlocal
  let : IsStrictlyHenselianLocalRing B := hstrict inferInstance
  have hinj : Function.Injective (algebraMap R B) := by
    apply Function.Injective.of_comp (f := algebraMap B L)
    change Function.Injective ((algebraMap B L).comp (algebraMap R B))
    rw [← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have hnotfield : ¬IsField B := fun h ↦ not_isField R
    ((Algebra.IsIntegral.isField_iff_isField hinj).mpr h)
  let : IsDiscreteValuationRing B :=
    ((IsDiscreteValuationRing.TFAE B hnotfield).out 0 2).mpr
      (inferInstance : IsDedekindDomain B)
  let k := IsLocalRing.ResidueField R
  let l := IsLocalRing.ResidueField B
  let ι : k →+* l := IsLocalRing.ResidueField.map (algebraMap R B)
  let : Algebra k l := ι.toAlgebra
  let : Algebra.IsAlgebraic k l := halg
  let : IsPurelyInseparable k l := inferInstance
  have hchar : ringChar l = ringChar k := by
    exact (ringChar.eq l (ringChar k) (C := charP_of_injective_ringHom ι.injective _))
  have hpB : p = if ringChar l = 0 then 1 else ringChar l := by rw [hchar]; exact hp
  let S : Subgroup Gal(Ksep/K) :=
    ⨅ d : TameRoots.Order p, MulAction.stabilizer Gal(Ksep/K) (α d)
  let ρ : S →* Gal(L/K) := (AlgEquiv.restrictNormalHom L).comp S.subtype
  let G := ρ.range
  let A : G →* (B ≃+* B) :=
    (MulSemiringAction.toRingAut Gal(L/K) B).comp G.subtype
  have hA : Function.Injective A := by
    intro g h heq
    apply Subtype.ext
    have he : g.1.toRingHom = h.1.toRingHom := by
      apply IsFractionRing.ringHom_ext (A := B)
      intro b
      exact congrArg (fun e : B ≃+* B ↦ (e b : L)) heq
    exact AlgEquiv.ext fun x ↦ DFunLike.congr_fun he x
  have hres : ∀ (g : G) (b : B), IsLocalRing.residue B (A g b) =
      IsLocalRing.residue B b := by
    intro g b
    let : IsLocalHom (A g).toRingHom := IsLocalHom.of_surjective _ (A g).surjective
    let ψ : l →ₐ[k] l := {
      __ := (IsLocalRing.ResidueField.mapEquiv (A g)).toRingHom
      commutes' := by
        intro x
        obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
        change (IsLocalRing.ResidueField.map (A g).toRingHom)
          (ι (IsLocalRing.residue R r)) = ι (IsLocalRing.residue R r)
        rw [show ι (IsLocalRing.residue R r) =
          IsLocalRing.residue B (algebraMap R B r) from
          IsLocalRing.ResidueField.map_residue _ _]
        rw [IsLocalRing.ResidueField.map_residue]
        change IsLocalRing.residue B (A g (algebraMap R B r)) = _
        rw [show A g (algebraMap R B r) = algebraMap R B r from ?_]
        apply Subtype.ext
        exact (g.1).commutes (algebraMap R K r) }
    have hψ : ψ = AlgHom.id k l := Subsingleton.elim _ _
    exact congrArg (fun f : l →ₐ[k] l ↦ f (IsLocalRing.residue B b)) hψ
  obtain ⟨w, hw⟩ := exists_irreducible B
  have hπB : algebraMap R B π ≠ 0 := by simpa only [map_zero] using hinj.ne hπ.ne_zero
  obtain ⟨e, u, hu⟩ := eq_unit_mul_pow_irreducible hπB hw
  have he : 0 < e := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hunit : IsUnit (algebraMap R B π) := by simp [hu, hz]
    exact hπ.not_isUnit (isUnit_of_map_unit _ _ hunit)
  let q := if p = 1 then 1 else p ^ e.factorization p
  let n := e / q
  have hsplit : e = q * n := by
    dsimp [q, n]
    split_ifs with h
    · simp
    · exact (Nat.ordProj_mul_ordCompl_eq_self e p).symm
  have hnpos : 0 < n := by
    by_cases h : p = 1
    · simpa [n, q, h] using he
    · simpa [n, q, h] using Nat.ordCompl_pos p he.ne'
  have hncop : n.Coprime p := by
    by_cases h : p = 1
    · simp [h]
    · have hp' : p.Prime := by
        by_cases hc : ringChar k = 0
        · exact False.elim (h (by simpa [k, hc] using hp))
        · have hpk : p = ringChar k := by simpa [k, hc] using hp
          exact hpk ▸ (CharP.char_is_prime_or_zero k (ringChar k)).resolve_right hc
      simpa [n, q, h] using (Nat.coprime_ordCompl hp' he.ne').symm
  let d : TameRoots.Order p := ⟨n, hnpos, hncop⟩
  obtain ⟨b, hb⟩ := units_pow_surjective B n hnpos (tame_order_isUnit B p hpB d) u
  let β : B := (b : B) * w ^ q
  have hβ : β ^ n = algebraMap R B π := by
    dsimp [β]
    rw [mul_pow, ← Units.val_pow_eq_pow_val, hb, ← pow_mul, ← hsplit, ← hu]
  have hfix : ∀ g : G, A g β = β := by
    intro g
    obtain ⟨h, hh⟩ := g.2
    have hhα : h.1 (α d) = α d := by
      exact Subgroup.mem_iInf.mp h.2 d
    let j : B →+* Ksep := L.val.toRingHom.comp (algebraMap B L)
    have hj : Function.Injective j := L.val.injective.comp (IsFractionRing.injective B L)
    have hαne : α d ≠ 0 := by
      intro hz
      have hz' := hα d
      rw [hz, zero_pow hnpos.ne'] at hz'
      apply hπ.ne_zero
      apply IsFractionRing.injective R K
      apply (algebraMap K Ksep).injective
      simpa only [map_zero] using hz'.symm
    have hr : (j β / α d) ^ n = 1 := by
      rw [div_pow, ← map_pow, hβ, hα d]
      have hc : j (algebraMap R B π) = algebraMap K Ksep (algebraMap R K π) := rfl
      rw [hc]
      exact div_self (hα d ▸ pow_ne_zero n hαne)
    have hf := roots_fixed R K Ksep n hnpos (tame_order_isUnit R p hp d) _ hr h.1
    rw [map_div₀, hhα] at hf
    have hβfix := (div_left_inj' hαne).mp hf
    apply hj
    change (algebraMap L Ksep) ((g.1) (algebraMap B L β)) = j β
    rw [← hh]
    change ↑((h.1.restrictNormal L) (algebraMap B L β)) = j β
    rw [AlgEquiv.restrictNormal_apply]
    exact hβfix
  have hratio : ∀ g : G, ∃ a : Bˣ, A g w = (a : B) * w ∧
      IsLocalRing.residue B (a : B) = 1 := by
    intro g
    obtain ⟨a, ha⟩ := associated_of_irreducible B hw (hw.map (A g).toMulEquiv)
    have ha' : A g w = (a : B) * w := by simpa [mul_comm] using ha.symm
    have heq : A g (b : B) * (a : B) ^ q = b := by
      apply mul_right_cancel₀ (pow_ne_zero q hw.ne_zero)
      calc
        A g (b : B) * (a : B) ^ q * w ^ q = A g β := by
          dsimp [β]
          rw [map_mul, map_pow, ha', mul_pow, mul_assoc]
        _ = β := hfix g
        _ = (b : B) * w ^ q := rfl
    have hr : IsLocalRing.residue B (a : B) ^ q = 1 := by
      have hh := congrArg (IsLocalRing.residue B) heq
      rw [map_mul, hres, map_pow] at hh
      exact mul_left_cancel₀ (b.isUnit.map (IsLocalRing.residue B)).ne_zero
        (by simpa only [mul_one] using hh)
    refine ⟨a, ha', ?_⟩
    by_cases hp1 : p = 1
    · simpa [q, hp1] using hr
    · have hpk : p = ringChar k := by
        by_cases hc : ringChar k = 0
        · exact False.elim (hp1 (by simpa [k, hc] using hp))
        · simpa [k, hc] using hp
      have hpprime : p.Prime := hpk ▸
        (CharP.char_is_prime_or_zero k (ringChar k)).resolve_right (by
          intro hz; exact hp1 (by simpa [k, hz] using hp))
      let : Fact p.Prime := ⟨hpprime⟩
      let : CharP l p := hpk ▸ charP_of_injective_ringHom ι.injective (ringChar k)
      have hpow : IsLocalRing.residue B (a : B) ^ p ^ e.factorization p =
          (1 : l) ^ p ^ e.factorization p := by simpa [q, hp1] using hr
      exact (iterateFrobenius_inj l p _).eq_iff.mp hpow
  by_cases hp1 : p = 1
  · change IsPGroup p G
    rw [hp1, isPGroup_one_iff_subsingleton]
    apply subsingleton_of_forall_eq 1
    intro g
    by_contra hg
    have hc : ringChar k = 0 := by
      by_contra hc
      have hp' : p = ringChar k := by simpa [k, hc] using hp
      exact CharP.ringChar_ne_one (R := k) (hp'.symm.trans hp1)
    let : CharP l 0 := hc ▸ charP_of_injective_ringHom ι.injective (ringChar k)
    have hd := wild_order_dvd (IsLocalRing.residue B) 0 A hA w hw hres hratio g hg
    have hz : orderOf g = 0 := zero_dvd_iff.mp hd
    exact (orderOf_pos g).ne' hz
  · have hc : ringChar k ≠ 0 := by
      intro hc
      exact hp1 (by simpa [k, hc] using hp)
    have hp' : p = ringChar k := by simpa [k, hc] using hp
    let : Fact p.Prime := ⟨hp' ▸
      (CharP.char_is_prime_or_zero k (ringChar k)).resolve_right hc⟩
    let : CharP l p := hp' ▸ charP_of_injective_ringHom ι.injective (ringChar k)
    obtain ⟨a, ha⟩ := wild_card_pow p A hA w hw hres hratio
    exact IsPGroup.of_card ha


end IsDiscreteValuationRing
