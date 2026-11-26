/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import WeilConjectures.RingTheory.CoverModuleExact
import WeilConjectures.Algebra.Module.TorsionSubmoduleFlatBaseChangeIso
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Exactness of the formal glueing complex

For a flat ring map `R → S` inducing an isomorphism modulo `I = (f₁, …, fₜ)` and an `R`-module
`M`, the formal glueing complex of `M` is exact.

## Implementation details

Scalar extension is written `S ⊗[R] M`; the map `η` is `m ↦ 1 ⊗ m` and the overlap maps are the
universal lifts of `m ↦ m/1`. Vanishing in all localizations `M_{fᵢ}` is equivalent to being
`I`-power torsion, and injectivity and surjectivity of the base change map on `I`-power torsion
handle the kernel of the first map and the torsion part of a kernel element. For the remaining
part, after clearing denominators one gets a compatible family `xᵢ` with `1 ⊗ xᵢ = fᵢⁿ y`; its
class in `Mᵗ / range (m ↦ (fᵢⁿ m)ᵢ)` is `I`-power torsion and vanishes after base change, hence
vanishes. This uses the ambient cokernel instead of Koszul homology.

## References

* [Stacks, Tag 05EK]
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace RingTheory

private theorem mem_primaryComponent_iff_localizations_zero
    {R : Type u} [CommRing R] {P : Type w} [AddCommGroup P] [Module R P]
    (t : ℕ) (f : Fin t → R) (x : P) :
    x ∈ Ideal.primaryComponent P (Ideal.span (Set.range f)) ↔
      ∀ i, LocalizedModule.mkLinearMap (Submonoid.powers (f i)) P x = 0 := by
  let I := Ideal.span (Set.range f)
  let J := (Submodule.span R ({x} : Set P)).annihilator
  constructor
  · intro hx i
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem P I x).mp hx
    apply (IsLocalizedModule.eq_zero_iff (Submonoid.powers (f i))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) P)).mpr
    refine ⟨⟨(f i) ^ n, ⟨n, rfl⟩⟩, ?_⟩
    have hn' := (Submodule.mem_torsionBySet_iff (↑(I ^ n) : Set R) x).mp hn
    have hfi : f i ∈ I := Ideal.subset_span ⟨i, rfl⟩
    exact hn' ⟨(f i) ^ n, Ideal.pow_mem_pow hfi n⟩
  · intro hx
    have hIJ : I ≤ J.radical := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (f i))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) P)).mp (hx i)
      obtain ⟨n, hn⟩ := a.2
      change ∃ n : ℕ, (f i) ^ n ∈ J
      refine ⟨n, (Submodule.mem_annihilator_span_singleton x _).mpr ?_⟩
      simpa only [← hn, Submonoid.smul_def] using ha
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIJ
      (Submodule.fg_span (Set.finite_range f))
    apply (Ideal.primaryComponent_mem P I x).mpr
    refine ⟨n, (Submodule.mem_torsionBySet_iff (↑(I ^ n) : Set R) x).mpr ?_⟩
    intro a
    exact (Submodule.mem_annihilator_span_singleton x (a : R)).mp (hn a.2)

private theorem formalGlueing_normalize
    {R : Type u} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]
    {P : Type v} [AddCommGroup P] [Module R P]
    (η : M →ₗ[R] P) (t : ℕ) (f : Fin t → R)
    (y : P) (s : ∀ i, LocalizedModule.Away (f i) M)
    (hb : ∀ i, LocalizedModule.mkLinearMap (Submonoid.powers (f i)) P y =
      IsLocalizedModule.map (Submonoid.powers (f i))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) P) η (s i))
    (hs : ∀ i j,
      IsLocalizedModule.lift (Submonoid.powers (f i))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j)) M)
        (localizationAway_map_units_of_dvd (M := M) _ _ (dvd_mul_right _ _)) (s i) =
      IsLocalizedModule.lift (Submonoid.powers (f j))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f j)) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j)) M)
        (localizationAway_map_units_of_dvd (M := M) _ _ (dvd_mul_left _ _)) (s j)) :
    ∃ n : ℕ, ∃ x : Fin t → M,
      (∀ i, (f i) ^ n • s i =
        LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M (x i)) ∧
      (∀ i j, (f j) ^ n • x i = (f i) ^ n • x j) ∧
      (∀ i, η (x i) = (f i) ^ n • y) := by
  classical
  let loc (a : R) := LocalizedModule.mkLinearMap (Submonoid.powers a) M
  let locP (a : R) := LocalizedModule.mkLinearMap (Submonoid.powers a) P
  let ρ := fun (a h : R) (ha : a ∣ h) ↦
    IsLocalizedModule.lift (Submonoid.powers a) (loc a) (loc h)
      (localizationAway_map_units_of_dvd (M := M) a h ha)
  have hrep (i : Fin t) : ∃ e : ℕ, ∃ m : M, (f i) ^ e • s i = loc (f i) m := by
    obtain ⟨⟨m, a⟩, ha⟩ := IsLocalizedModule.surj (Submonoid.powers (f i)) (loc (f i)) (s i)
    obtain ⟨e, he⟩ := a.2
    exact ⟨e, m, by simpa only [← he, Submonoid.smul_def] using ha⟩
  choose e x hx using hrep
  let N := Finset.univ.sup e
  let m (i : Fin t) := (f i) ^ (N - e i) • x i
  have hm (i : Fin t) : (f i) ^ N • s i = loc (f i) (m i) := by
    dsimp only [m]
    rw [map_smul, ← hx, smul_smul, ← pow_add,
      Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ i))]
  have heq (i j : Fin t) : ∃ k : ℕ,
      (f i * f j) ^ k • ((f j) ^ N • m i) =
        (f i * f j) ^ k • ((f i) ^ N • m j) := by
    have hloc : loc (f i * f j) ((f j) ^ N • m i) =
        loc (f i * f j) ((f i) ^ N • m j) := by
      rw [(loc (f i * f j)).map_smul ((f j) ^ N) (m i),
        (loc (f i * f j)).map_smul ((f i) ^ N) (m j)]
      rw [← IsLocalizedModule.lift_apply (Submonoid.powers (f i)) (loc (f i))
        (loc (f i * f j)) (localizationAway_map_units_of_dvd (M := M) _ _
          (dvd_mul_right (f i) (f j))) (m i)]
      rw [← IsLocalizedModule.lift_apply (Submonoid.powers (f j)) (loc (f j))
        (loc (f i * f j)) (localizationAway_map_units_of_dvd (M := M) _ _
          (dvd_mul_left (f j) (f i))) (m j)]
      change (f j) ^ N • ρ (f i) (f i * f j) (dvd_mul_right _ _) (loc (f i) (m i)) =
        (f i) ^ N • ρ (f j) (f i * f j) (dvd_mul_left _ _) (loc (f j) (m j))
      rw [← hm, ← hm, map_smul, map_smul, hs, smul_comm]
    obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers (f i * f j))
      (loc (f i * f j))).mp hloc
    obtain ⟨k, hk⟩ := a.2
    exact ⟨k, by simpa only [← hk, Submonoid.smul_def] using ha⟩
  have heqP (i : Fin t) : ∃ c : ℕ,
      (f i) ^ c • ((f i) ^ N • y) = (f i) ^ c • η (m i) := by
    have hloc : locP (f i) ((f i) ^ N • y) = locP (f i) (η (m i)) := by
      rw [map_smul, hb]
      rw [← IsLocalizedModule.map_apply (Submonoid.powers (f i)) (loc (f i))
        (locP (f i)) η (m i), ← hm, map_smul]
    obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers (f i))
      (locP (f i))).mp hloc
    obtain ⟨c, hc⟩ := a.2
    exact ⟨c, by simpa only [← hc, Submonoid.smul_def] using ha⟩
  choose k hk using heq
  choose c hc using heqP
  let K := (Finset.univ.sup fun p : Fin t × Fin t ↦ k p.1 p.2) ⊔ Finset.univ.sup c
  have hK (i j : Fin t) :
      (f i * f j) ^ K • ((f j) ^ N • m i) =
        (f i * f j) ^ K • ((f i) ^ N • m j) := by
    have hle : k i j ≤ K := le_sup_of_le_left (Finset.le_sup
      (f := fun p : Fin t × Fin t ↦ k p.1 p.2) (Finset.mem_univ (i, j)))
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, mul_smul, hk]
  have hKP (i : Fin t) : (f i) ^ K • ((f i) ^ N • y) = (f i) ^ K • η (m i) := by
    have hle : c i ≤ K := le_sup_of_le_right (Finset.le_sup (Finset.mem_univ i))
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, mul_smul, hc]
  refine ⟨K + N, fun i ↦ (f i) ^ K • m i, ?_, ?_, ?_⟩
  · intro i
    change (f i) ^ (K + N) • s i = loc (f i) ((f i) ^ K • m i)
    rw [pow_add, mul_smul, hm, (loc (f i)).map_smul ((f i) ^ K) (m i)]
  · intro i j
    have h := hK i j
    simp only [smul_smul] at h ⊢
    calc
      _ = ((f i * f j) ^ K * (f j) ^ N) • m i := by congr 1; rw [mul_pow, pow_add]; ring
      _ = ((f i * f j) ^ K * (f i) ^ N) • m j := h
      _ = _ := by congr 1; rw [mul_pow, pow_add]; ring
  · intro i
    rw [map_smul, ← hKP, pow_add, mul_smul]

/-- A compatible family of multiples by powers of the generators is a boundary if
it becomes a boundary after the flat base change: if `f_j^n x_i = f_i^n x_j` for all `i, j`
and `1 ⊗ x_i = f_i^n y` in `S ⊗_R M`, then `x_i = f_i^n m` for some `m ∈ M`. -/
private theorem formalGlueing_powerFamily_descent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (hflat : RingHom.Flat (algebraMap R S))
    (t : ℕ) (f : Fin t → R)
    (hquot : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map))
    (M : Type w) [AddCommGroup M] [Module R M]
    (n : ℕ) (x : Fin t → M) (y : S ⊗[R] M)
    (hcompat : ∀ i j, (f j) ^ n • x i = (f i) ^ n • x j)
    (hboundary : ∀ i, TensorProduct.mk R S M 1 (x i) = (f i) ^ n • y) :
    ∃ m : M, ∀ i, x i = (f i) ^ n • m := by
  classical
  let I := Ideal.span (Set.range f)
  let δ : M →ₗ[R] (Fin t → M) := LinearMap.pi fun i ↦
    (f i) ^ n • (LinearMap.id : M →ₗ[R] M)
  let Q := (Fin t → M) ⧸ LinearMap.range δ
  let π : (Fin t → M) →ₗ[R] Q := (LinearMap.range δ).mkQ
  let ξ : Q := π x
  let J := (Submodule.span R ({ξ} : Set Q)).annihilator
  have hkill (k : Fin t) : (f k) ^ n • ξ = 0 := by
    change (f k) ^ n • π x = 0
    rw [← map_smul]
    have heq : (f k) ^ n • x = δ (x k) := by
      funext i
      exact hcompat i k
    rw [heq]
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range δ)).mpr ⟨x k, rfl⟩
  have hIJ : I ≤ J.radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ∃ e : ℕ, (f i) ^ e ∈ J
    exact ⟨n, (Submodule.mem_annihilator_span_singleton ξ _).mpr (hkill i)⟩
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIJ
    (Submodule.fg_span (Set.finite_range f))
  have hξ : ξ ∈ Ideal.primaryComponent Q I := by
    apply (Ideal.primaryComponent_mem Q I ξ).mpr
    refine ⟨e, (Submodule.mem_torsionBySet_iff (↑(I ^ e) : Set R) ξ).mpr ?_⟩
    intro a
    exact (Submodule.mem_annihilator_span_singleton ξ (a : R)).mp (he a.2)
  let E := TensorProduct.piRight R R S (fun _ : Fin t ↦ M)
  have hδ (z : S ⊗[R] M) (i : Fin t) : E (δ.lTensor S z) i = (f i) ^ n • z := by
    induction z using TensorProduct.inductionOn with
    | tmul a m =>
      simp [E, δ, TensorProduct.piRightHom_tmul, TensorProduct.tmul_smul]
    | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂, smul_add]
  have hboundary' : (1 : S) ⊗ₜ[R] x = δ.lTensor S y := by
    apply E.injective
    funext i
    rw [hδ]
    exact hboundary i
  have hπδ : π.comp δ = 0 := by
    ext m
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range δ)).mpr ⟨m, rfl⟩
  have hzero : (1 : S) ⊗ₜ[R] ξ = 0 := by
    change (1 : S) ⊗ₜ[R] π x = 0
    rw [← LinearMap.lTensor_tmul, hboundary', ← LinearMap.lTensor_comp_apply,
      hπδ, LinearMap.lTensor_zero, LinearMap.zero_apply]
  have hinj := (Ideal.primaryComponent_baseChange_bijective I
    (Submodule.fg_span (Set.finite_range f)) hflat hquot Q).1
  have hclass : (⟨ξ, hξ⟩ : Ideal.primaryComponent Q I) = 0 := by
    apply hinj
    apply Subtype.ext
    change (1 : S) ⊗ₜ[R] ξ = (1 : S) ⊗ₜ[R] (0 : Q)
    simpa only [TensorProduct.tmul_zero] using hzero
  have hξzero : ξ = 0 := congrArg Subtype.val hclass
  obtain ⟨m, hm⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range δ)).mp hξzero
  exact ⟨m, fun i ↦ (congrFun hm i).symm⟩


/-- The formal glueing complex is exact for a flat map inducing an isomorphism modulo
`I = (f₁, …, fₜ)`: the sequence
`0 → M → (S ⊗_R M) × ∏ᵢ M_{fᵢ} → ∏ᵢ (S ⊗_R M)_{fᵢ} × ∏ᵢⱼ M_{fᵢfⱼ}` is exact. -/
theorem formalGlueingComplexExact {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (hflat : φ.Flat)
    (t : ℕ) (f : Fin t → R)
    (hquot : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map φ) φ Ideal.le_comap_map))
    (M : Type w) [AddCommGroup M] [Module R M] :
    letI : Algebra R S := φ.toAlgebra
    let η : M →ₗ[R] S ⊗[R] M := TensorProduct.mk R S M 1
    let ρ := fun (a h : R) (ha : a ∣ h) ↦
      IsLocalizedModule.lift (Submonoid.powers a)
        (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers h) M)
        (localizationAway_map_units_of_dvd (M := M) a h ha)
    let α : M → (S ⊗[R] M) × (∀ i : Fin t, LocalizedModule.Away (f i) M) :=
      fun m ↦ (η m, fun i ↦ LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M m)
    let β : (S ⊗[R] M) × (∀ i : Fin t, LocalizedModule.Away (f i) M) →
        (∀ i : Fin t, LocalizedModule.Away (f i) (S ⊗[R] M)) ×
          (∀ i j : Fin t, LocalizedModule.Away (f i * f j) M) :=
      fun p ↦
        (fun i ↦ LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (S ⊗[R] M) p.1 -
          IsLocalizedModule.map (Submonoid.powers (f i))
            (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M)
            (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (S ⊗[R] M)) η (p.2 i),
         fun i j ↦ ρ (f i) (f i * f j) (dvd_mul_right (f i) (f j)) (p.2 i) -
          ρ (f j) (f i * f j) (dvd_mul_left (f j) (f i)) (p.2 j))
    Function.Injective α ∧ Function.Exact α β := by
  classical
  let : Algebra R S := φ.toAlgebra
  let η : M →ₗ[R] S ⊗[R] M := TensorProduct.mk R S M 1
  let loc (a : R) := LocalizedModule.mkLinearMap (Submonoid.powers a) M
  let locS (a : R) := LocalizedModule.mkLinearMap (Submonoid.powers a) (S ⊗[R] M)
  let I := Ideal.span (Set.range f)
  have htors := Ideal.primaryComponent_baseChange_bijective I
    (Submodule.fg_span (Set.finite_range f)) hflat hquot M
  dsimp only
  constructor
  · intro m₁ m₂ heq
    have hη : η (m₁ - m₂) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg Prod.fst heq
    have hloc : ∀ i, loc (f i) (m₁ - m₂) = 0 := by
      intro i
      rw [map_sub, sub_eq_zero]
      exact congrArg (fun p ↦ p.2 i) heq
    have hmem := (mem_primaryComponent_iff_localizations_zero t f (m₁ - m₂)).mpr hloc
    have hz : (⟨m₁ - m₂, hmem⟩ : Ideal.primaryComponent M I) = 0 := by
      apply htors.1
      apply Subtype.ext
      change η (m₁ - m₂) = η 0
      rw [map_zero]
      exact hη
    exact sub_eq_zero.mp (congrArg Subtype.val hz)
  · intro p
    constructor
    · intro hp
      have hb : ∀ i, locS (f i) p.1 =
          IsLocalizedModule.map (Submonoid.powers (f i)) (loc (f i)) (locS (f i)) η
            (p.2 i) := by
        intro i
        exact sub_eq_zero.mp (congrArg (fun q ↦ q.1 i) hp)
      have hs : ∀ i j,
          IsLocalizedModule.lift (Submonoid.powers (f i)) (loc (f i)) (loc (f i * f j))
            (localizationAway_map_units_of_dvd (M := M) _ _ (dvd_mul_right _ _)) (p.2 i) =
          IsLocalizedModule.lift (Submonoid.powers (f j)) (loc (f j)) (loc (f i * f j))
            (localizationAway_map_units_of_dvd (M := M) _ _ (dvd_mul_left _ _)) (p.2 j) := by
        intro i j
        exact sub_eq_zero.mp (congrArg (fun q ↦ q.2 i j) hp)
      obtain ⟨n, x, hx, hcompat, hη⟩ := formalGlueing_normalize η t f p.1 p.2 hb hs
      obtain ⟨m, hm⟩ := formalGlueing_powerFamily_descent hflat t f hquot M n x p.1
        hcompat hη
      have hmloc : ∀ i, loc (f i) m = p.2 i := by
        intro i
        apply IsLocalizedModule.smul_injective (loc (f i))
          (⟨(f i) ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (f i))
        change (f i) ^ n • loc (f i) m = (f i) ^ n • p.2 i
        rw [hx, hm, map_smul]
      have hrem : p.1 - η m ∈ Ideal.primaryComponent (S ⊗[R] M) I := by
        apply (mem_primaryComponent_iff_localizations_zero t f _).mpr
        intro i
        apply (IsLocalizedModule.eq_zero_iff (Submonoid.powers (f i)) (locS (f i))).mpr
        refine ⟨⟨(f i) ^ n, ⟨n, rfl⟩⟩, ?_⟩
        change (f i) ^ n • (p.1 - η m) = 0
        rw [smul_sub, sub_eq_zero, ← hη, hm, map_smul]
      obtain ⟨z, hz⟩ := htors.2 ⟨p.1 - η m, hrem⟩
      have hzη : η (z : M) = p.1 - η m := congrArg Subtype.val hz
      have hzloc : ∀ i, loc (f i) (z : M) = 0 :=
        (mem_primaryComponent_iff_localizations_zero t f (z : M)).mp z.2
      refine ⟨m + (z : M), ?_⟩
      apply Prod.ext
      · change η (m + (z : M)) = p.1
        rw [map_add, hzη, add_sub_cancel]
      · funext i
        change loc (f i) (m + (z : M)) = p.2 i
        rw [map_add, hzloc, add_zero, hmloc]
    · rintro ⟨m, rfl⟩
      apply Prod.ext
      · funext i
        simp only [IsLocalizedModule.map_apply, sub_self, Pi.zero_apply, Prod.fst_zero]
      · funext i j
        simp only [IsLocalizedModule.lift_apply, sub_self, Pi.zero_apply, Prod.snd_zero]

end RingTheory
