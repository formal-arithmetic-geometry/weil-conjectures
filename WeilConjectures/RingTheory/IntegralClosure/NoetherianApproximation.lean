/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.MixedCharZero
public import Mathlib.Algebra.CharP.Quotient
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.ZariskisMainTheorem
public import WeilConjectures.Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Noetherian normal local subrings of a normal local domain

Every finite subset of an integrally closed local domain `A` is contained in a Noetherian
integrally closed local subring `P ⊆ A` dominated by `A`
(`IsLocalRing.exists_subring_isNoetherianRing_isIntegrallyClosed`). This is the local input of
the reduction of the spreading theorem (blueprint `sbc-thm-spreading-finite-etale-galois`,
[Stacks 0EZJ]) to a Noetherian base.

The subring `P` is the localization at `𝔪_A` of the integral closure `C` of a polynomial ring
`B ⊆ A` in a finite extension of `Frac B`; `C ⊆ A` as `A` is normal, and `C` is finite over `B`
(`IsLocalRing.exists_subring_of_isIntegral`).
- If `A` contains a field `k` (equal characteristic), `B` is a Noether normalization of `k[E]`
  and `C` is finite by Noether's finiteness theorem (`IsLocalRing.exists_subring_of_field`).
- In mixed characteristic `(0, p)`, `B = ℤ[X₁, …, Xₘ]` maps to lifts of a Noether normalization
  of `ℤ[E] / p`. Then `ℤ[E]` is quasi-finite over `B` at `𝔪_A ∩ ℤ[E]`, so by Zariski's main
  theorem every element of `E` is a quotient of elements integral over `B` with denominator a
  unit of `A`; `C` is finite as `Frac ℤ[E]` is separable over `Frac B`
  (`IsLocalRing.exists_subring_of_mixedCharZero`).

## Main statements

- `IsLocalRing.exists_subring_isNoetherianRing_isIntegrallyClosed`
- `MvPolynomial.injective_of_injective_map_zmod`: a map `ℤ[X] → D` which is injective modulo `p`
  is injective.
-/

@[expose] public section

open IsLocalRing

namespace MvPolynomial

/-- Let `β : ℤ[X] → D` be a map to a domain in which the prime `p` is nonzero. If `β` reduces
modulo `p` to an injective map `𝔽_p[X] → D'`, then `β` is injective. -/
theorem injective_of_injective_map_zmod {σ D D' : Type*} [CommRing D] [IsDomain D] [CommRing D']
    (p : ℕ) [Fact p.Prime] (hp : (p : D) ≠ 0) (β : MvPolynomial σ ℤ →+* D)
    (ψ : MvPolynomial σ (ZMod p) →+* D') (hψ : Function.Injective ψ) (π : D →+* D')
    (h : π.comp β = ψ.comp (map (Int.castRingHom (ZMod p)))) :
    Function.Injective β := by
  have key (n : ℕ) (f : MvPolynomial σ ℤ) (hf : β f = 0) : C ((p : ℤ) ^ n) ∣ f := by
    induction n generalizing f with
    | zero => simp
    | succ n ih =>
      have hmap : map (Int.castRingHom (ZMod p)) f = 0 := hψ (by
        rw [map_zero, ← RingHom.comp_apply, ← h, RingHom.comp_apply, hf, map_zero])
      obtain ⟨f₁, rfl⟩ : C (p : ℤ) ∣ f := (C_dvd_iff_dvd_coeff _ _).mpr fun i ↦ by
        have := congr(coeff i $hmap)
        rw [coeff_map, coeff_zero] at this
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp this
      have hf₁ : β f₁ = 0 := by
        rw [map_mul, ← RingHom.comp_apply, eq_intCast, Int.cast_natCast] at hf
        exact (mul_eq_zero.mp hf).resolve_left hp
      obtain ⟨f₂, rfl⟩ := ih f₁ hf₁
      exact ⟨f₂, by rw [pow_succ', C_mul, mul_assoc]⟩
  refine (injective_iff_map_eq_zero β).mpr fun f hf ↦ ?_
  ext i
  rw [coeff_zero]
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    ((C_dvd_iff_dvd_coeff _ _).mp (key (f.coeff i).natAbs f hf) i) ?_
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self (Fact.out : p.Prime).one_lt

end MvPolynomial

namespace IsLocalRing

variable {A C : Type*} [CommRing A] [IsLocalRing A] [CommRing C] [IsDomain C]

/-- If `ι : C → A` is an injective map from a Noetherian normal domain to a local ring, the image
`P` of the localization of `C` at `ι⁻¹ 𝔪_A` is a Noetherian normal local subring of `A` dominated
by `A`, containing every quotient `ι c / ι s` with `ι s ∉ 𝔪_A`. -/
theorem exists_subring_of_injective [IsNoetherianRing C] [IsIntegrallyClosed C] (ι : C →+* A)
    (hι : Function.Injective ι) :
    ∃ P : Subring A, IsNoetherianRing P ∧ IsLocalRing P ∧ IsIntegrallyClosed P ∧
      IsLocalHom P.subtype ∧
      ∀ (c s : C) (a : A), ι s ∉ maximalIdeal A → ι s * a = ι c → a ∈ P := by
  set q := (maximalIdeal A).comap ι
  let R := Localization.AtPrime q
  have hunit (s : q.primeCompl) : IsUnit (ι s) := by
    by_contra h
    exact s.2 (by simpa [q] using h)
  let φ : R →+* A := IsLocalization.lift (M := q.primeCompl) hunit
  have hle : q.primeCompl ≤ nonZeroDivisors C := q.primeCompl_le_nonZeroDivisors
  have hφ : Function.Injective φ := by
    rw [IsLocalization.lift_injective_iff]
    simp [(IsLocalization.injective R hle).eq_iff, hι.eq_iff]
  let e : R ≃+* φ.range := RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun x y h ↦ hφ congr($h.1), φ.rangeRestrict_surjective⟩
  have := IsLocalization.isNoetherianRing q.primeCompl R inferInstance
  refine ⟨φ.range, isNoetherianRing_of_ringEquiv R e, .of_surjective' _ e.surjective, ?_, ?_, ?_⟩
  · have := isIntegrallyClosed_of_isLocalization R q.primeCompl hle
    exact IsIntegrallyClosed.of_equiv e
  · constructor
    intro x hx
    obtain ⟨r, rfl⟩ := e.surjective x
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl r
    have hcs : ι c = ι s * φ (IsLocalization.mk' R c s) :=
      (IsLocalization.lift_mk'_spec _ _ _ _).mp rfl
    have hc : c ∉ q := by
      intro hc
      refine (mem_maximalIdeal _).mp hc ?_
      rw [hcs]
      exact (hunit s).mul hx
    exact IsUnit.map e ((IsLocalization.AtPrime.isUnit_mk'_iff R q c s).mpr hc)
  · intro c s a hs h
    exact ⟨IsLocalization.mk' R c (⟨s, hs⟩ : q.primeCompl),
      (IsLocalization.lift_mk'_spec _ _ _ _).mpr h.symm⟩


/-- Let `B → A` be an injective map from a Noetherian domain to a normal local domain such that
integral closures of `B` in finite extensions of its fraction field are finite over `B`. If every
element `e` of a finite set `E ⊆ A` is a quotient `(g e) / g` of elements integral over `B` with
`g` a unit of `A`, then `E` is contained in a Noetherian normal local subring of `A` dominated
by `A`. -/
theorem exists_subring_of_isIntegral.{v} {A : Type v} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegrallyClosed A] (B : Type*) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Algebra B A] (hB : Function.Injective (algebraMap B A))
    (hfin : ∀ (L : Type v) [Field L] [Algebra (FractionRing B) L] [Algebra B L]
      [IsScalarTower B (FractionRing B) L] [FiniteDimensional (FractionRing B) L],
      Module.Finite B (integralClosure B L))
    {E : Set A} (hE : E.Finite)
    (hg : ∀ e ∈ E, ∃ g ∉ maximalIdeal A, IsIntegral B g ∧ IsIntegral B (g * e)) :
    ∃ P : Subring A, E ⊆ P ∧ IsNoetherianRing P ∧ IsLocalRing P ∧ IsIntegrallyClosed P ∧
      IsLocalHom P.subtype := by
  classical
  choose! g hgm hgi hgei using hg
  let F := FractionRing A
  let K := FractionRing B
  have : IsScalarTower B A F := inferInstance
  have : FaithfulSMul B F := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (by rw [IsScalarTower.algebraMap_eq B A F]; exact (IsFractionRing.injective A F).comp hB)
  let : Algebra K F := FractionRing.liftAlgebra B F
  have : IsScalarTower B K F := FractionRing.isScalarTower_liftAlgebra B F
  let S : Set F := (fun e ↦ algebraMap A F (g e)) '' E ∪ (fun e ↦ algebraMap A F (g e * e)) '' E
  have hSint (x : F) (hx : x ∈ S) : IsIntegral B x := by
    rcases hx with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
    · exact (hgi e he).map (IsScalarTower.toAlgHom B A F)
    · exact (hgei e he).map (IsScalarTower.toAlgHom B A F)
  let L := IntermediateField.adjoin K S
  have : Finite S := ((hE.image _).union (hE.image _)).to_subtype
  have : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x hx ↦ (hSint x hx).tower_top
  have : IsScalarTower B L F := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply B K F x, IsScalarTower.algebraMap_apply B K L x]
    rfl
  let C := integralClosure B L
  have := hfin L
  have : IsNoetherianRing C := IsNoetherianRing.of_finite B C
  have : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  let ψ : C →+* F := (algebraMap L F).comp (algebraMap C L)
  have hψi (x : C) : IsIntegral B (ψ x) := x.2.map (IsScalarTower.toAlgHom B L F)
  have hψ (x : C) : ψ x ∈ (algebraMap A F).range :=
    IsIntegrallyClosed.isIntegral_iff.mp (hψi x).tower_top
  let eA : A ≃+* (algebraMap A F).range := RingEquiv.ofBijective (algebraMap A F).rangeRestrict
    ⟨fun x y h ↦ IsFractionRing.injective A F congr($h.1),
      (algebraMap A F).rangeRestrict_surjective⟩
  let ι : C →+* A := eA.symm.toRingHom.comp (ψ.codRestrict _ hψ)
  have hιF (x : C) : algebraMap A F (ι x) = ψ x := congr($(eA.apply_symm_apply ⟨ψ x, hψ x⟩).1)
  have hι : Function.Injective ι := fun x y h ↦ by
    have := congr(algebraMap A F $h)
    rw [hιF, hιF] at this
    exact Subtype.ext ((algebraMap L F).injective this)
  obtain ⟨P, hPn, hPl, hPi, hPh, hP⟩ := exists_subring_of_injective ι hι
  refine ⟨P, fun e he ↦ ?_, hPn, hPl, hPi, hPh⟩
  have hmem (a : A) (ha : algebraMap A F a ∈ S) : ∃ c : C, ι c = a := by
    have : IsIntegral B (⟨algebraMap A F a, IntermediateField.subset_adjoin K S ha⟩ : L) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom B L F) (algebraMap L F).injective).mp
        (hSint _ ha)
    exact ⟨⟨_, this⟩, IsFractionRing.injective A F (hιF _)⟩
  obtain ⟨s, hs⟩ := hmem (g e) (Or.inl ⟨e, he, rfl⟩)
  obtain ⟨c, hc⟩ := hmem (g e * e) (Or.inr ⟨e, he, rfl⟩)
  exact hP c s e (hs ▸ hgm e he) (by rw [hs, hc])


/-- Equal characteristic case: if the normal local domain `A` contains a field `k`, every finite
subset of `A` is contained in a Noetherian normal local subring of `A` dominated by `A`. This
uses Noether normalization and Noether's finiteness theorem. -/
theorem exists_subring_of_field (k : Type*) [Field k] {A : Type*} [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsIntegrallyClosed A] [Algebra k A] {E : Set A} (hE : E.Finite) :
    ∃ P : Subring A, E ⊆ P ∧ IsNoetherianRing P ∧ IsLocalRing P ∧ IsIntegrallyClosed P ∧
      IsLocalHom P.subtype := by
  let D := Algebra.adjoin k E
  have : Algebra.FiniteType k D :=
    (Subalgebra.fg_iff_finiteType D).mp (Subalgebra.fg_def.mpr ⟨E, hE, rfl⟩)
  obtain ⟨s, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k D
  let B := MvPolynomial (Fin s) k
  let : Algebra B D := φ.toRingHom.toAlgebra
  have : Module.Finite B D := hfin
  let : Algebra B A := (D.val.toRingHom.comp φ.toRingHom).toAlgebra
  have : IsScalarTower B D A := .of_algebraMap_eq fun _ ↦ rfl
  refine exists_subring_of_isIntegral B (Subtype.val_injective.comp hinj)
    (fun L _ _ _ _ _ ↦ MvPolynomial.finite_integralClosure (FractionRing B) L) hE
    fun e he ↦ ⟨1, (maximalIdeal A).ne_top_iff_one.mp (maximalIdeal.isMaximal A).ne_top,
      isIntegral_one, ?_⟩
  rw [one_mul]
  exact (Algebra.IsIntegral.isIntegral (R := B) (⟨e, Algebra.subset_adjoin he⟩ : D)).map
    (IsScalarTower.toAlgHom B D A)


/-- Mixed characteristic case: if the normal local domain `A` has characteristic zero and the
prime `p` lies in its maximal ideal, every finite subset of `A` is contained in a Noetherian
normal local subring of `A` dominated by `A`. The proof applies Zariski's main theorem to
`ℤ[X₁, …, Xₘ] → ℤ[E]`, where the `Xᵢ` map to lifts of a Noether normalization of `ℤ[E] / p`. -/
theorem exists_subring_of_mixedCharZero {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegrallyClosed A] [CharZero A] (p : ℕ) [Fact p.Prime] (hp : (p : A) ∈ maximalIdeal A)
    {E : Set A} (hE : E.Finite) :
    ∃ P : Subring A, E ⊆ P ∧ IsNoetherianRing P ∧ IsLocalRing P ∧ IsIntegrallyClosed P ∧
      IsLocalHom P.subtype := by
  classical
  let D := Algebra.adjoin ℤ E
  have : Algebra.FiniteType ℤ D :=
    (Subalgebra.fg_iff_finiteType D).mp (Subalgebra.fg_def.mpr ⟨E, hE, rfl⟩)
  let I : Ideal D := Ideal.span {(p : D)}
  have hpD : (p : D) ∈ nonunits D := fun h ↦ (mem_maximalIdeal _).mp hp (by
    simpa using h.map D.val)
  have hp0 : (p : D) ≠ 0 := fun h ↦ (Nat.cast_ne_zero (R := A)).mpr (Fact.out : p.Prime).ne_zero
    (by simpa using congr(D.val $h))
  have : CharP (D ⧸ I) p := CharP.quotient D p hpD
  have : Nontrivial (D ⧸ I) := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).one_lt.ne'
  let : Algebra (ZMod p) (D ⧸ I) := ZMod.algebra _ p
  have : Algebra.FiniteType (ZMod p) (D ⧸ I) :=
    .of_restrictScalars_finiteType ℤ (ZMod p) (D ⧸ I)
  obtain ⟨m, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg (ZMod p) (D ⧸ I)
  choose y hy using fun i : Fin m ↦ Ideal.Quotient.mk_surjective (I := I) (φ (MvPolynomial.X i))
  let B := MvPolynomial (Fin m) ℤ
  let β : B →+* D := MvPolynomial.eval₂Hom (Int.castRingHom D) y
  have hcomm : (Ideal.Quotient.mk I).comp β =
      φ.toRingHom.comp (MvPolynomial.map (Int.castRingHom (ZMod p))) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) fun i ↦ ?_
    · simp [β]
    · simp [β, hy]
  have hβ : Function.Injective β := MvPolynomial.injective_of_injective_map_zmod p hp0 β
    φ.toRingHom hinj (Ideal.Quotient.mk I) hcomm
  let : Algebra B D := β.toAlgebra
  let : Algebra B A := (D.val.toRingHom.comp β).toAlgebra
  have : IsScalarTower B D A := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.FiniteType B D := .of_restrictScalars_finiteType ℤ B D
  let 𝔭 : Ideal D := (maximalIdeal A).comap D.val.toRingHom
  have : Algebra.WeaklyQuasiFiniteAt B 𝔭 := by
    have hIJ : I ≤ (𝔭.under B).map (algebraMap B D) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      have : (p : B) ∈ 𝔭.under B := by simpa [𝔭] using hp
      simpa using Ideal.mem_map_of_mem (algebraMap B D) this
    let B' := MvPolynomial (Fin m) (ZMod p)
    let : Algebra B B' := (MvPolynomial.map (Int.castRingHom (ZMod p))).toAlgebra
    have : Module.Finite B B' :=
      RingHom.Finite.of_surjective _ (MvPolynomial.map_surjective _ ZMod.intCast_surjective)
    let : Algebra B' (D ⧸ I) := φ.toRingHom.toAlgebra
    have : Module.Finite B' (D ⧸ I) := hfin
    have : IsScalarTower B B' (D ⧸ I) := .of_algebraMap_eq fun x ↦ DFunLike.congr_fun hcomm x
    have : Module.Finite B (D ⧸ I) := .trans B' (D ⧸ I)
    have : Module.Finite B (D ⧸ (𝔭.under B).map (algebraMap B D)) :=
      .of_surjective (Ideal.Quotient.factorₐ B hIJ).toLinearMap
        (Ideal.Quotient.factor_surjective hIJ)
    infer_instance
  obtain ⟨r, hr, hri, hrx⟩ := Algebra.zariskisMainProperty_iff.mp
    (Algebra.ZariskisMainProperty.of_finiteType_of_weaklyQuasiFiniteAt (R := B) 𝔭)
  refine exists_subring_of_isIntegral B (Subtype.val_injective.comp hβ)
    (fun L _ _ _ _ _ ↦ IsIntegralClosure.finite B (FractionRing B) L (integralClosure B L)) hE
    fun e he ↦ ?_
  obtain ⟨n, hn⟩ := hrx ⟨e, Algebra.subset_adjoin he⟩
  refine ⟨(r : A) ^ n, fun h ↦ hr ((maximalIdeal.isMaximal A).isPrime.mem_of_pow_mem n h),
    (hri.pow n).map (IsScalarTower.toAlgHom B D A), ?_⟩
  simpa using hn.map (IsScalarTower.toAlgHom B D A)


/-- **Noetherian approximation of a normal local domain** (used in the reduction of blueprint
`sbc-thm-spreading-finite-etale-galois` to a Noetherian base, [Stacks 0EZJ]): every finite subset
`E` of an integrally closed local domain `A` is contained in a subring `P ⊆ A` which is a
Noetherian integrally closed local domain such that `P → A` is a local homomorphism, i.e.
`𝔪_A ∩ P = 𝔪_P` (see `IsLocalRing.maximalIdeal_comap`).

The ring `P` is a localization of the integral closure of a polynomial ring `B` in a finite
extension of `Frac B`: in equal characteristic `B` is a Noether normalization of `k[E]` for the
prime field `k ⊆ A`, and in mixed characteristic `(0, p)` it is `ℤ[X₁, …, Xₘ]`, mapping to lifts
of a Noether normalization of `ℤ[E] / p` (Zariski's main theorem). -/
theorem exists_subring_isNoetherianRing_isIntegrallyClosed {A : Type*} [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsIntegrallyClosed A] {E : Set A} (hE : E.Finite) :
    ∃ P : Subring A, E ⊆ P ∧ IsNoetherianRing P ∧ IsLocalRing P ∧ IsIntegrallyClosed P ∧
      IsLocalHom P.subtype := by
  refine split_by_characteristic_localRing A (fun p hpp hchar ↦ ?_)
    (fun _ ↦ exists_subring_of_field ℚ hE) (fun p hp hmixed ↦ ?_)
  · have : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero A p).resolve_right hpp.ne_zero⟩
    let := ZMod.algebra A p
    exact exists_subring_of_field (ZMod p) hE
  · have : Fact p.Prime := ⟨hp⟩
    have : CharZero A := hmixed.toCharZero
    obtain ⟨I, hI, hchar⟩ := hmixed.charP_quotient
    refine exists_subring_of_mixedCharZero p (le_maximalIdeal hI ?_) hE
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p

end IsLocalRing
