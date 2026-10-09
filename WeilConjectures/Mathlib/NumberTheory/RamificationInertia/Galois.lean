/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import WeilConjectures.Mathlib.RingTheory.Invariant.Profinite

/-!
# Inertia groups and unramified intermediate extensions

Let `T / S / R` be a tower of domains, `G` a finite Galois group of `T / R` and `H ≤ G` a Galois
group of `T / S`. If the inertia group `I_G(P)` of a prime `P` of `T` is contained in `H`, then
the prime `P ∩ S` of `S` is unramified over `R`
(`Ideal.ramificationIdx_under_eq_one_of_inertia_le`): the inertia groups of `P` in `G` and `H`
then coincide, and their orders are the ramification indices `e(P | R)` and `e(P | S)`, while
`e(P | R) = e(P ∩ S | R) e(P | S)`.

Let `Ω` be a Galois extension of the fraction field `K` of a Dedekind domain `R`, and `Q` a maximal
ideal of the integral closure of `R` in `Ω`. If the inertia group of `Q` in `Gal(Ω / K)` fixes the
images of all `R`-algebra maps from a Dedekind domain `T` finite over `R` to `Ω`, then all primes
of `T` over `Q ∩ R` are unramified (`Ideal.ramificationIdx_eq_one_of_forall_inertia`): this is
reduced to the Galois closure of the image of `T`, using that inertia lifts from finite Galois
subextensions to `Ω` (`Ideal.exists_mem_inertia_eqOn`).
-/

@[expose] public section

namespace Ideal

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
  [Algebra R T] [IsScalarTower R S T] [IsDomain R] [IsDomain S] [IsDomain T]
  [Module.Finite R T] [Module.Finite S T] [Module.Flat R T] [Module.Flat S T]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G T] [IsGaloisGroup G R T]
  (H : Subgroup G) [IsGaloisGroup H S T]

/-- **Primes below the inertia field are unramified.** If the inertia group of a prime `P` of
`T` in `Gal(T / R)` is contained in `Gal(T / S)`, then `P ∩ S` is unramified over `R`. -/
theorem ramificationIdx_under_eq_one_of_inertia_le (p : Ideal R) [p.IsPrime] (P : Ideal T)
    [P.IsPrime] [P.LiesOver p] [PerfectField p.ResidueField]
    [PerfectField (P.under S).ResidueField] (h : P.inertia G ≤ H) :
    (P.under S).ramificationIdx R = 1 := by
  have hG : Nat.card (P.inertia G) = P.ramificationIdx R := by
    rw [card_inertia_eq_ramificationIdxIn p P, ramificationIdxIn_eq_ramificationIdx p P G]
  have hH : Nat.card (P.inertia H) = P.ramificationIdx S := by
    rw [card_inertia_eq_ramificationIdxIn (P.under S) P,
      ramificationIdxIn_eq_ramificationIdx (P.under S) P H]
  have hGH : Nat.card (P.inertia H) = Nat.card (P.inertia G) := by
    have : P.inertia H = (P.inertia G).subgroupOf H := rfl
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have htower := ramificationIdx_tower (R := R) (P.under S) P
  have hne : P.ramificationIdx R ≠ 0 := by
    rw [← hG]
    exact Nat.card_pos.ne'
  rw [← hH, hGH, hG] at htower
  exact (mul_eq_right₀ hne).1 htower.symm

end Ideal

section SeparableClosure

open IntermediateField

variable {R K Ω : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
  [IsGalois K Ω]

namespace Ideal

/-- The map from a ring `T` with an `R`-algebra map `ψ : T → Ω` to the integral closure of `R`
in `Ω`, for `T` integral over `R`. -/
noncomputable def integralClosureMap {T : Type*} [CommRing T] [Algebra R T]
    [Algebra.IsIntegral R T] (ψ : T →ₐ[R] Ω) : T →+* integralClosure R Ω :=
  (ψ.codRestrict (integralClosure R Ω) fun x ↦
    (Algebra.IsIntegral.isIntegral (R := R) x).map ψ).toRingHom

omit [IsDedekindDomain R] [IsFractionRing R K] [IsGalois K Ω] in
@[simp]
lemma coe_integralClosureMap {T : Type*} [CommRing T] [Algebra R T] [Algebra.IsIntegral R T]
    (ψ : T →ₐ[R] Ω) (x : T) : (integralClosureMap ψ x : Ω) = ψ x :=
  rfl

omit [IsFractionRing R K] [IsGalois K Ω] in
/-- An `R`-algebra map from a domain integral over `R` to `Ω` is injective. -/
lemma injective_of_isIntegral {T : Type*} [CommRing T] [IsDomain T] [Algebra R T]
    [Algebra.IsIntegral R T] (ψ : T →ₐ[R] Ω) (hR : Function.Injective (algebraMap R Ω)) :
    Function.Injective ψ := by
  refine (injective_iff_map_eq_zero ψ).2 fun x hx ↦ ?_
  have hker : RingHom.ker ψ.toRingHom = ⊥ := by
    refine Ideal.eq_bot_of_comap_eq_bot (R := R) ?_
    ext r
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes, Ideal.mem_bot]
    exact map_eq_zero_iff _ hR
  have : x ∈ RingHom.ker ψ.toRingHom := hx
  rwa [hker, Ideal.mem_bot] at this

set_option maxHeartbeats 1000000 in
/-- **Primes of a cover fixed by inertia are unramified.** Let `T` be a Dedekind domain finite
over `R`, with an `R`-algebra map `ψ : T → Ω`, and `Q` a maximal ideal of the integral closure of
`R` in `Ω` over a maximal ideal `m` of `R` with finite residue field. If the inertia group of `Q`
in `Gal(Ω / K)` fixes `ψ(T)` pointwise, then the prime `ψ⁻¹ Q` of `T` is unramified over `R`. -/
theorem ramificationIdx_comap_integralClosureMap_eq_one {T : Type*} [CommRing T] [IsDomain T]
    [IsDedekindDomain T] [Algebra R T] [Module.Finite R T] [Module.IsTorsionFree R T]
    (ψ : T →ₐ[R] Ω) (Q : Ideal (integralClosure R Ω)) [Q.IsMaximal] (m : Ideal R)
    [m.IsMaximal] [Q.LiesOver m] [Finite (R ⧸ m)]
    (hI : ∀ σ ∈ Q.inertia Gal(Ω/K), ∀ x, σ (ψ x) = ψ x) :
    (Q.comap (integralClosureMap ψ)).ramificationIdx R = 1 := by
  have : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  -- the field `L'` generated by `ψ(T)` and its Galois closure `M`
  let L' : IntermediateField K Ω := adjoin K (Set.range ψ)
  have : FiniteDimensional K L' := by
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := T)
    have : L' = adjoin K (ψ '' s) := by
      refine le_antisymm (adjoin_le_iff.2 ?_) (adjoin.mono _ _ _ (Set.image_subset_range _ _))
      rintro _ ⟨x, rfl⟩
      have hx : x ∈ Submodule.span R (s : Set T) := hs ▸ Submodule.mem_top
      refine Submodule.span_induction (p := fun x _ ↦ ψ x ∈ adjoin K (ψ '' s)) ?_ ?_ ?_ ?_ hx
      · exact fun y hy ↦ subset_adjoin _ _ ⟨y, hy, rfl⟩
      · simp
      · intro a b _ _ ha hb
        rw [map_add]
        exact add_mem ha hb
      · intro r a _ ha
        rw [map_smul, algebra_compatible_smul K r]
        exact (adjoin K (ψ '' s)).smul_mem ha
    rw [this]
    refine finiteDimensional_adjoin fun y hy ↦ ?_
    exact (Algebra.IsIntegral.isIntegral (R := K) y)
  let M := normalClosure K L' Ω
  have hL'M : L' ≤ M := le_normalClosure L'
  -- the integral closure of `R` in `M`, with its Galois group
  let TM := integralClosure R M
  have : IsFractionRing TM M := integralClosure.isFractionRing_of_finite_extension K M
  have : Module.Finite R TM := IsIntegralClosure.finite R K M TM
  have : IsDedekindDomain TM := integralClosure.isDedekindDomain R K M
  have : IsGaloisGroup Gal(M/K) R TM := IsGaloisGroup.of_isFractionRing _ _ _ K M
  -- the subfield `L'` of `M`, its ring of integers `S` and its Galois group `H`
  let LM : IntermediateField K M := restrict hL'M
  let H : Subgroup Gal(M/K) := fixingSubgroup Gal(M/K) (LM : Set M)
  let S := integralClosure R LM
  have : IsFractionRing S LM := integralClosure.isFractionRing_of_finite_extension K LM
  have : Module.Finite R S := IsIntegralClosure.finite R K LM S
  have : IsDedekindDomain S := integralClosure.isDedekindDomain R K LM
  have : IsScalarTower R LM M := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R K LM, IsScalarTower.algebraMap_apply R K M]
    rfl
  let iST : S →+* TM := ((IsScalarTower.toAlgHom R LM M).domRestrict
    (integralClosure R LM) |>.codRestrict (integralClosure R M) fun x ↦
      x.2.map (IsScalarTower.toAlgHom R LM M)).toRingHom
  let _ : Algebra S TM := iST.toAlgebra
  let _ : SMul S TM := Algebra.toSMul
  have : IsScalarTower S TM M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R S TM := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsIntegral R TM := Algebra.IsIntegral.of_finite R TM
  have : Algebra.IsIntegral S TM := Algebra.IsIntegral.tower_top R
  have : IsGaloisGroup H S TM := IsGaloisGroup.of_isFractionRing H S TM LM M
  have : Module.Finite S TM := Module.Finite.of_restrictScalars_finite R S TM
  -- `ψ` lands in the ring of integers `S` of `L'`
  have hψL' (x : T) : ψ x ∈ L' := subset_adjoin _ _ ⟨x, rfl⟩
  let ψM : T →ₐ[R] M := ψ.codRestrict ((M.toSubalgebra).restrictScalars R) fun x ↦ hL'M (hψL' x)
  let ψLM : T →ₐ[R] LM := ψM.codRestrict ((LM.toSubalgebra).restrictScalars R) fun x ↦
    (mem_restrict hL'M _).2 (hψL' x)
  let jTS : T →ₐ[R] S := ψLM.codRestrict ((integralClosure R LM)) fun x ↦
    (Algebra.IsIntegral.isIntegral (R := R) x).map ψLM
  let _ : Algebra T S := jTS.toRingHom.toAlgebra
  have : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq fun r ↦ (jTS.commutes r).symm
  have hRΩ : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  have hψinj : Function.Injective ψ := injective_of_isIntegral ψ hRΩ
  have hjinj : Function.Injective (algebraMap T S) := fun x y hxy ↦
    hψinj (congrArg (fun z : S ↦ ((z : LM) : M) : S → Ω) hxy)
  have : Module.IsTorsionFree T S :=
    Module.isTorsionFree_iff_faithfulSMul.2 ((faithfulSMul_iff_algebraMap_injective T S).2 hjinj)
  -- the prime `P` of `TM` below `Q`
  let iTB : TM →+* integralClosure R Ω :=
    integralClosureMap ((M.val.restrictScalars R).comp (integralClosure R M).val)
  let P : Ideal TM := Q.comap iTB
  have hiTB : iTB.comp (algebraMap R TM) = algebraMap R (integralClosure R Ω) := by
    ext r
    change ((algebraMap R M r : M) : Ω) = algebraMap R Ω r
    rw [IsScalarTower.algebraMap_apply R K M, IsScalarTower.algebraMap_apply R K Ω]
    rfl
  have hPm : P.LiesOver m := ⟨by
    rw [Ideal.under, Ideal.comap_comap, hiTB, Ideal.over_def Q m]⟩
  have hcomp : iTB.comp ((algebraMap S TM).comp (algebraMap T S)) = integralClosureMap ψ := by
    ext x
    rfl
  have : (P.under S).LiesOver (Q.comap (integralClosureMap ψ)) := ⟨by
    rw [Ideal.under, Ideal.under, Ideal.comap_comap, Ideal.comap_comap, ← hcomp]⟩
  -- the inertia group of `P` fixes `L'`
  have hle : P.inertia Gal(M/K) ≤ H := by
    intro τ hτ
    obtain ⟨τ', hτ'⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (E := Ω) τ
    have hτ'M (x : M) : τ' (x : Ω) = (τ x : Ω) := by
      rw [← hτ']
      exact (AlgEquiv.restrictNormal_commutes τ' M x).symm
    obtain ⟨σ, hσ, hσM⟩ := exists_mem_inertia_eqOn M Q τ' fun b hb ↦ by
      let t : TM := ⟨⟨b, hb⟩,
        (isIntegral_algHom_iff (M.val.restrictScalars R) Subtype.val_injective).1 b.2⟩
      have ht := hτ t
      have hiτ : iTB (τ • t) = τ' • b := Subtype.ext (hτ'M ⟨b, hb⟩).symm
      have : iTB (τ • t - t) ∈ Q := ht
      rwa [map_sub, hiτ] at this
    have hσL' : L' ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      refine adjoin_le_iff.2 ?_
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro f hf
      have hst : σ ∈ MulAction.stabilizer Gal(Ω/K) (ψ x) := hI σ hσ x
      exact (Subgroup.zpowers_le.2 hst) hf
    rw [_root_.mem_fixingSubgroup_iff]
    intro x hx
    apply Subtype.ext
    have hxL' : (x : Ω) ∈ L' := (mem_restrict hL'M x).1 hx
    have h1 : σ (x : Ω) = x :=
      (IntermediateField.mem_fixedField_iff _ _).1 (hσL' hxL') σ (Subgroup.mem_zpowers σ)
    change (τ x : Ω) = x
    rw [← hτ'M, ← hσM _ x.2, h1]
  have hperf : PerfectField m.ResidueField := by
    have : Finite m.ResidueField :=
      Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField m).2
    exact PerfectField.ofFinite
  have : (P.under S).IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (P.under S) m
  have hperfS : PerfectField (P.under S).ResidueField := by
    have : Finite (S ⧸ P.under S) := Module.finite_of_finite (R ⧸ m)
    have : Finite (P.under S).ResidueField :=
      Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField (P.under S)).2
    exact PerfectField.ofFinite
  have : Module.IsTorsionFree R TM := Module.isTorsionFree_iff_faithfulSMul.2
    ((faithfulSMul_iff_algebraMap_injective R TM).2 fun x y hxy ↦ hRΩ (by
      have h := congrArg iTB hxy
      have hx := RingHom.congr_fun hiTB x
      have hy := RingHom.congr_fun hiTB y
      simp only [RingHom.comp_apply] at hx hy
      rw [hx, hy] at h
      exact congrArg Subtype.val h))
  have : Module.IsTorsionFree S TM := Module.isTorsionFree_iff_faithfulSMul.2
    ((faithfulSMul_iff_algebraMap_injective S TM).2 fun x y hxy ↦
      Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun z : TM ↦ ((z : M) : Ω)) hxy))))
  have hS := Ideal.ramificationIdx_under_eq_one_of_inertia_le (S := S) H m P hle
  have htower := Ideal.ramificationIdx_tower (R := R) (Q.comap (integralClosureMap ψ)) (P.under S)
  rw [hS] at htower
  exact (mul_eq_one.1 htower.symm).1

/-- **Covers on which inertia acts trivially are unramified.** Let `T` be a Dedekind domain finite
over `R` with an `R`-algebra map to `Ω`, and `Q` a maximal ideal of the integral closure of `R`
in `Ω` over a maximal ideal `m` of `R` with finite residue field. If the inertia group of `Q` in
`Gal(Ω / K)` fixes the image of every `R`-algebra map `T → Ω`, then every prime of `T` over `m` is
unramified over `R`. -/
theorem ramificationIdx_eq_one_of_forall_inertia {T : Type*} [CommRing T] [IsDomain T]
    [IsDedekindDomain T] [Algebra R T] [Module.Finite R T] [Module.IsTorsionFree R T]
    (ψ₀ : T →ₐ[R] Ω) (Q : Ideal (integralClosure R Ω)) [Q.IsMaximal] (m : Ideal R)
    [m.IsMaximal] [Q.LiesOver m] [Finite (R ⧸ m)]
    (hI : ∀ σ ∈ Q.inertia Gal(Ω/K), ∀ (ψ : T →ₐ[R] Ω) (x : T), σ (ψ x) = ψ x)
    (𝔭 : Ideal T) [𝔭.IsPrime] [𝔭.LiesOver m] : 𝔭.ramificationIdx R = 1 := by
  have : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  let B := integralClosure R Ω
  let φ₀ := integralClosureMap ψ₀
  let _ : Algebra T B := φ₀.toAlgebra
  have : IsScalarTower R T B := IsScalarTower.of_algebraMap_eq fun r ↦ Subtype.ext (by
    change algebraMap R Ω r = ψ₀ (algebraMap R T r)
    rw [ψ₀.commutes])
  have : Algebra.IsIntegral T B := Algebra.IsIntegral.tower_top R
  have hker : (⊥ : Ideal B).comap (algebraMap T B) ≤ 𝔭 := by
    intro x hx
    have hx' : ψ₀ x = 0 := congrArg Subtype.val hx
    have hRΩ : Function.Injective (algebraMap R Ω) := by
      rw [IsScalarTower.algebraMap_eq R K Ω]
      exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
    rw [injective_of_isIntegral ψ₀ hRΩ (hx'.trans (map_zero ψ₀).symm)]
    exact 𝔭.zero_mem
  obtain ⟨Q', -, hQ', hQ'𝔭⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔭 ⊥ hker
  -- `Q'` is a conjugate `g • Q` of `Q`
  have hIC : IsIntegrallyClosedIn R K := inferInstance
  let _ : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  have := Algebra.continuousSMul_integralClosure R K Ω
  have := Algebra.isInvariant_integralClosure R K Ω
  have hunder : Q.under R = Q'.under R := by
    rw [← Ideal.over_def Q m, Ideal.under, IsScalarTower.algebraMap_eq R T B, ← Ideal.comap_comap,
      hQ'𝔭, Ideal.over_def 𝔭 m]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (G := Gal(Ω/K))
    Q Q' hunder
  let ψ : T →ₐ[R] Ω := ((g⁻¹ : Gal(Ω/K)).toAlgHom.restrictScalars R).comp ψ₀
  have hψ : Q.comap (integralClosureMap ψ) = 𝔭 := by
    rw [← hQ'𝔭, hg]
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  rw [← hψ]
  exact ramificationIdx_comap_integralClosureMap_eq_one ψ Q m fun σ hσ x ↦ hI σ hσ ψ x

end Ideal

end SeparableClosure
