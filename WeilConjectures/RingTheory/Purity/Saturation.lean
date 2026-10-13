/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Regular.RegularSequence
public import WeilConjectures.RingTheory.Regular.Hartogs

/-!
# Sections over the complement of a closed subset

Let `A` be a ring, `𝔞 ⊆ A` an ideal, `L` an `A`-algebra and `T ⊆ L` an `A`-subalgebra. The
*saturation* of `T` with respect to `𝔞` is the subalgebra
`Subalgebra.idealSaturation 𝔞 T = {t ∈ L | ∀ g ∈ 𝔞, ∃ n, gⁿ t ∈ T}`.
When the nonzero elements of a domain `A` act invertibly on `L` (e.g. `L` is the localization of
an `A`-algebra `M` at the nonzero elements of `A` and `T` is the image of `M`), this is the ring of
sections of `T` over the complement `U` of `V(𝔞)` in `Spec A`.

## Main results

- `Subalgebra.awayTensorIdealSaturationEquiv`: for `g ∈ 𝔞`, the inclusion
  `T ⊆ idealSaturation 𝔞 T` becomes
  an isomorphism after inverting `g` (`T → idealSaturation 𝔞 T` is an isomorphism over `U`).
- `Subalgebra.finite_idealSaturation`: if `A` is a Noetherian domain with a regular pair `a, b ∈ 𝔞`
  (i.e. `V(𝔞)` has depth at least two) and `T` is a finite `A`-module, then so is its saturation.
- `Subalgebra.isWeaklyRegular_idealSaturation`: if moreover `T` is flat over `U`, then every regular
  pair of `A` is weakly regular on the saturation.

These are the algebraic forms of the finiteness and depth properties of `j_* (M~|_U)` for a
coherent sheaf `M~` on `Spec A` which is flat over `U`, see [Stacks 0BK3]. They are used in the
proof of Zariski–Nagata purity, an input of blueprint `sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

open TensorProduct RingTheory.Sequence
open scoped Pointwise

namespace RingTheory.Sequence

/-- A weakly regular sequence of `R` is weakly regular on every flat `R`-module. -/
lemma IsWeaklyRegular.of_flat_module {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [Module.Flat R N] {rs : List R} (h : IsWeaklyRegular R rs) : IsWeaklyRegular N rs :=
  ((TensorProduct.rid R N).isWeaklyRegular_congr rs).1 h.isWeaklyRegular_lTensor

/-- The first element of a weakly regular pair on a nontrivial module is nonzero. -/
lemma IsWeaklyRegular.ne_zero_of_pair {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Nontrivial M] {a b : R} (h : IsWeaklyRegular M [a, b]) : a ≠ 0 := by
  rintro rfl
  obtain ⟨x, y, hxy⟩ := exists_pair_ne M
  rw [isWeaklyRegular_cons_iff] at h
  exact hxy (h.1 (by simp))

end RingTheory.Sequence

namespace Subalgebra

variable {A L : Type*} [CommRing A] [CommRing L] [Algebra A L]

/-- The saturation of the subalgebra `T ⊆ L` with respect to the ideal `𝔞`: the elements `t` of
`L` such that for every `g ∈ 𝔞` some power `gⁿ t` lies in `T`. Geometrically, the sections of `T`
over the complement of `V(𝔞)`. -/
def idealSaturation (𝔞 : Ideal A) (T : Subalgebra A L) : Subalgebra A L where
  carrier := {t | ∀ g ∈ 𝔞, ∃ n : ℕ, g ^ n • t ∈ T}
  mul_mem' {s t} hs ht g hg := by
    obtain ⟨n₁, h₁⟩ := hs g hg
    obtain ⟨n₂, h₂⟩ := ht g hg
    refine ⟨n₁ + n₂, ?_⟩
    rw [pow_add, ← smul_mul_smul_comm]
    exact T.mul_mem h₁ h₂
  add_mem' {s t} hs ht g hg := by
    obtain ⟨n₁, h₁⟩ := hs g hg
    obtain ⟨n₂, h₂⟩ := ht g hg
    refine ⟨n₁ + n₂, ?_⟩
    have e₁ : g ^ (n₁ + n₂) • s = g ^ n₂ • g ^ n₁ • s := by rw [← mul_smul, ← pow_add, add_comm]
    have e₂ : g ^ (n₁ + n₂) • t = g ^ n₁ • g ^ n₂ • t := by rw [← mul_smul, ← pow_add]
    rw [smul_add, e₁, e₂]
    exact T.add_mem (T.smul_mem h₁ _) (T.smul_mem h₂ _)
  algebraMap_mem' r g _ := ⟨0, by simp⟩

variable (𝔞 : Ideal A) (T : Subalgebra A L)

lemma mem_idealSaturation_iff {t : L} :
    t ∈ idealSaturation 𝔞 T ↔ ∀ g ∈ 𝔞, ∃ n : ℕ, g ^ n • t ∈ T :=
  Iff.rfl

lemma le_idealSaturation : T ≤ idealSaturation 𝔞 T := fun t ht _ _ ↦ ⟨0, by simpa using ht⟩

/-- For `g ∈ 𝔞`, the inclusion of `T` into its saturation becomes bijective after inverting
`g`. -/
lemma bijective_map_inclusion_idealSaturation {g : A} (hg : g ∈ 𝔞) :
    Function.Bijective (Algebra.TensorProduct.map
      (AlgHom.id (Localization.Away g) (Localization.Away g))
      (inclusion (le_idealSaturation 𝔞 T))) := by
  set Ag := Localization.Away g
  have hfun :
      ⇑(Algebra.TensorProduct.map (AlgHom.id Ag Ag) (inclusion (le_idealSaturation 𝔞 T))) =
      ⇑((inclusion (le_idealSaturation 𝔞 T)).toLinearMap.lTensor Ag) := by
    funext x
    induction x with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨?_, fun y ↦ ?_⟩
  · rw [hfun]
    exact Module.Flat.lTensor_preserves_injective_linearMap _
      (inclusion_injective (le_idealSaturation 𝔞 T))
  · induction y with
    | zero => exact ⟨0, map_zero _⟩
    | tmul x t =>
      obtain ⟨n, hn⟩ := t.2 g hg
      have hu : IsUnit (algebraMap A Ag (g ^ n)) := by
        rw [map_pow]
        exact (IsLocalization.Away.algebraMap_isUnit g).pow n
      refine ⟨(↑hu.unit⁻¹ * x) ⊗ₜ ⟨g ^ n • (t : L), hn⟩, ?_⟩
      have ht : inclusion (le_idealSaturation 𝔞 T) ⟨g ^ n • (t : L), hn⟩ = g ^ n • t := rfl
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ht, ← TensorProduct.smul_tmul,
        Algebra.smul_def, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩

/-- For `g ∈ 𝔞`, the inclusion `T ⊆ idealSaturation 𝔞 T` induces an isomorphism after inverting
`g`. -/
noncomputable def awayTensorIdealSaturationEquiv {g : A} (hg : g ∈ 𝔞) :
    Localization.Away g ⊗[A] T ≃ₐ[Localization.Away g]
      Localization.Away g ⊗[A] idealSaturation 𝔞 T :=
  AlgEquiv.ofBijective _ (bijective_map_inclusion_idealSaturation 𝔞 T hg)

variable {𝔞 T}

/-- **Finiteness of the saturation.** Let `A` be a Noetherian domain whose nonzero elements act
invertibly on `L`, and let `a, b ∈ 𝔞` be a weakly regular pair of `A`. If `T` is a finite
`A`-module, then so is its saturation with respect to `𝔞`. -/
theorem finite_idealSaturation [IsNoetherianRing A] [IsDomain A]
    (hL : ∀ c : A, c ≠ 0 → IsUnit (algebraMap A L c)) {a b : A} (ha : a ∈ 𝔞) (hb : b ∈ 𝔞)
    (hab : IsWeaklyRegular A [a, b]) [Module.Finite A T] :
    Module.Finite A (idealSaturation 𝔞 T) := by
  classical
  have ha0 : a ≠ 0 := hab.ne_zero_of_pair
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := T)
  set v : Fin n → L := fun i ↦ (s i : L)
  obtain ⟨I, hI, hmax⟩ := exists_maximal_linearIndepOn A v
  set F : Submodule A L := Submodule.span A (Set.range fun i : I ↦ v i)
  have hc (i : Fin n) : ∃ c : A, c ≠ 0 ∧ c • v i ∈ F := by
    by_cases hi : i ∈ I
    · exact ⟨1, one_ne_zero, by
        rw [one_smul]
        exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩⟩
    · obtain ⟨c, hc0, hcF⟩ := hmax i hi
      rw [Set.image_eq_range] at hcF
      exact ⟨c, hc0, hcF⟩
  choose c hc0 hcF using hc
  set c₀ := ∏ i, c i
  have hc₀ : c₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ hc0 i
  -- `c₀ T ⊆ F`
  have hT (x : T) : c₀ • (x : L) ∈ F := by
    have hx : x ∈ Submodule.span A (Set.range s) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have : c₀ = (∏ j ∈ Finset.univ.erase i, c j) * c i := by
        rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      rw [this, mul_smul]
      exact F.smul_mem _ (hcF i)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Subalgebra.coe_add, smul_add]
      exact F.add_mem hx hy
    | smul r x _ hx =>
      rw [Subalgebra.coe_smul, smul_comm]
      exact F.smul_mem r hx
  -- `F` is free, so `[a, b]` is weakly regular on `F`
  have : Module.Free A F := Module.Free.of_basis (Module.Basis.span hI)
  obtain ⟨haF, hbF⟩ := (IsWeaklyRegular.of_flat_module (N := F) hab).isSMulRegular_and_mem_smul_top
  -- `c₀ (idealSaturation 𝔞 T) ⊆ F`
  have key (t : L) (ht : t ∈ idealSaturation 𝔞 T) : c₀ • t ∈ F := by
    obtain ⟨k, hk⟩ := ht a ha
    obtain ⟨l, hl⟩ := ht b hb
    set p : F := ⟨a ^ k • c₀ • t, by rw [smul_comm]; exact hT ⟨_, hk⟩⟩
    set q : F := ⟨b ^ l • c₀ • t, by rw [smul_comm]; exact hT ⟨_, hl⟩⟩
    have hpq : b ^ l • p = a ^ k • q := Subtype.ext (by
      simp only [p, q, Submodule.coe_smul]
      rw [smul_comm (b ^ l)])
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
      (mem_pow_smul_top_of_pow_smul_mem haF hbF k l
        (by rw [hpq]; exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top))
    have hu : IsUnit (algebraMap A L (a ^ k)) := hL _ (pow_ne_zero _ ha0)
    have : c₀ • t = (y : L) := by
      apply hu.mul_left_cancel
      rw [← Algebra.smul_def, ← Algebra.smul_def]
      have := congrArg Subtype.val hy
      simp only [Submodule.coe_smul, p] at this
      exact this.symm
    rw [this]
    exact y.2
  let φ : idealSaturation 𝔞 T →ₗ[A] F :=
    { toFun t := ⟨c₀ • (t : L), key t t.2⟩
      map_add' x y := Subtype.ext (by simp [smul_add])
      map_smul' r x := Subtype.ext (by simp [smul_comm c₀ r]) }
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    apply (hL c₀ hc₀).mul_left_cancel
    rw [← Algebra.smul_def, ← Algebra.smul_def]
    exact congrArg Subtype.val hxy
  have : Module.Finite A F := Module.Finite.span_of_finite A (Set.finite_range _)
  exact Module.Finite.of_injective φ hφ

/-- **Depth of the saturation.** Let `A` be a domain whose nonzero elements act invertibly on
`L`, and assume that `T` is flat over the complement of `V(𝔞)`, i.e. `A_g ⊗ T` is `A`-flat for
`g ∈ 𝔞`. Then every weakly regular pair of `A` is weakly regular on the saturation of `T`. -/
theorem isWeaklyRegular_idealSaturation [IsDomain A]
    (hL : ∀ c : A, c ≠ 0 → IsUnit (algebraMap A L c)) {a b : A} (hab : IsWeaklyRegular A [a, b])
    (hflat : ∀ g ∈ 𝔞, Module.Flat A (Localization.Away g ⊗[A] T)) :
    IsWeaklyRegular (idealSaturation 𝔞 T) [a, b] := by
  have ha0 : a ≠ 0 := hab.ne_zero_of_pair
  have hua := hL a ha0
  have key (m : idealSaturation 𝔞 T) (hm : b • m ∈ a • (⊤ : Submodule A (idealSaturation 𝔞 T))) :
      m ∈ a • (⊤ : Submodule A (idealSaturation 𝔞 T)) := by
    obtain ⟨s, -, hs⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
    set u : L := ↑hua.unit⁻¹ * (m : L)
    have hu : algebraMap A L a * u = m := by
      simp only [u, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
    have huS : u ∈ idealSaturation 𝔞 T := by
      intro g hg
      obtain ⟨n₁, h₁⟩ := m.2 g hg
      obtain ⟨n₂, h₂⟩ := s.2 g hg
      have hm₀ : g ^ (n₁ + n₂) • (m : L) ∈ T := by
        rw [add_comm, pow_add, mul_smul]
        exact T.smul_mem h₁ _
      have hs₀ : g ^ (n₁ + n₂) • (s : L) ∈ T := by
        rw [pow_add, mul_smul]
        exact T.smul_mem h₂ _
      set m₀ : T := ⟨_, hm₀⟩
      set s₀ : T := ⟨_, hs₀⟩
      have h0 : b • m₀ = a • s₀ := Subtype.ext (by
        have := congrArg Subtype.val hs
        simp only [Subalgebra.coe_smul] at this
        simp only [m₀, s₀, Subalgebra.coe_smul]
        rw [smul_comm b, smul_comm a, this])
      have := hflat g hg
      obtain ⟨-, hX⟩ := (IsWeaklyRegular.of_flat_module
        (N := Localization.Away g ⊗[A] T) hab).isSMulRegular_and_mem_smul_top
      have hmem : (1 : Localization.Away g) ⊗ₜ m₀ ∈
          a • (⊤ : Submodule A (Localization.Away g ⊗[A] T)) := hX _ (by
        rw [← TensorProduct.tmul_smul, h0, TensorProduct.tmul_smul]
        exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
      obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hmem
      obtain ⟨⟨w₀, ⟨_, j, rfl⟩⟩, hw₀⟩ := IsLocalizedModule.surj (Submonoid.powers g)
        (TensorProduct.mk A (Localization.Away g) T 1) w
      simp only [Submonoid.smul_def] at hw₀
      have heq : TensorProduct.mk A (Localization.Away g) T 1 (g ^ j • m₀) =
          TensorProduct.mk A (Localization.Away g) T 1 (a • w₀) := by
        rw [map_smul, map_smul, ← hw₀, TensorProduct.mk_apply, ← hw, smul_comm]
      obtain ⟨⟨_, l, rfl⟩, hl⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers g) heq
      simp only [Submonoid.smul_def] at hl
      refine ⟨l + j + (n₁ + n₂), ?_⟩
      have : g ^ (l + j + (n₁ + n₂)) • u = ((g ^ l • w₀ : T) : L) := by
        apply hua.mul_left_cancel
        have hl' := congrArg Subtype.val hl
        simp only [Subalgebra.coe_smul, m₀] at hl'
        rw [← Algebra.smul_def, ← Algebra.smul_def, smul_comm, Algebra.smul_def a u, hu,
          pow_add, pow_add, mul_smul, mul_smul, hl', Subalgebra.coe_smul, smul_comm]
      rw [this]
      exact (g ^ l • w₀).2
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
      ⟨⟨u, huS⟩, Submodule.mem_top, Subtype.ext ?_⟩
    rw [Subalgebra.coe_smul, Algebra.smul_def]
    exact hu
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
  refine ⟨fun x y h ↦ Subtype.ext (hua.mul_left_cancel ?_), fun q₁ q₂ hq ↦ ?_⟩
  · rw [← Algebra.smul_def, ← Algebra.smul_def, ← Subalgebra.coe_smul, ← Subalgebra.coe_smul]
    exact congrArg Subtype.val h
  · obtain ⟨m₁, rfl⟩ := Submodule.Quotient.mk_surjective _ q₁
    obtain ⟨m₂, rfl⟩ := Submodule.Quotient.mk_surjective _ q₂
    simp only [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hq ⊢
    exact key _ (by rwa [smul_sub])

end Subalgebra
