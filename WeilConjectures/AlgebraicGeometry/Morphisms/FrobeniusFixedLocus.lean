/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.FrobeniusContracting

/-!
# Local points fixed by a lift of a Frobenius

Let `X₀` be a scheme over a finite field `k₀` with `q` elements, let `S = X₀ ×_{k₀} k` be its base
change to an algebraically closed field `k`, with projections `p : S ⟶ X₀` and `a : S ⟶ Spec k`,
and let `h` be a `k`-endomorphism of `S` lifting a `q ^ m`-power Frobenius `G` of `X₀`
(`h ≫ p = p ≫ G`), with `m ≥ 1`. If `t : Spec A ⟶ S` is a point with values in a local ring
fixed by `h`, then `t` is constant: it factors through a `k`-rational point `x` of `S` fixed by `h`
(`AlgebraicGeometry.exists_eq_comp_of_comp_eq_self_of_isFrobenius`).

The algebraic input is that in a local algebra `A` over an algebraically closed field `k`, an
element `r` with `r ^ N = r` is a scalar, when `r ↦ r ^ N` is a ring endomorphism and `N ≥ 2`
(`IsLocalRing.exists_algebraMap_eq_of_pow_eq_self`): `r` is congruent to a root `c` of
`X ^ N - X` in `k` modulo the maximal ideal, and `n = r - c` satisfies `n ^ N = n` with
`n ∈ 𝔪`, so `n (1 - n ^ (N - 1)) = 0` forces `n = 0`. This is the scheme-theoretic part of
blueprint `thm-trf-frobenius-fixed-points`: the fixed scheme of `h` is reduced.

## Main statements

- `IsLocalRing.exists_algebraMap_eq_of_pow_eq_self`: Frobenius-fixed elements of a local algebra
  over an algebraically closed field are scalars.
- `AlgebraicGeometry.exists_eq_comp_of_comp_eq_self_of_isFrobenius`: a local point fixed by `h`
  factors through a fixed rational point.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing Polynomial

/-- In a local algebra `A` over an algebraically closed field `K`, an element `r` with
`r ^ N = r` is a scalar, provided `N ≥ 2` and `r ↦ r ^ N` is a ring endomorphism of `A`. -/
lemma IsLocalRing.exists_algebraMap_eq_of_pow_eq_self {K A : Type*} [Field K] [IsAlgClosed K]
    [CommRing A] [IsLocalRing A] [Algebra K A] {N : ℕ} (hN : 2 ≤ N) (χ : A →+* A)
    (hχ : ∀ r, χ r = r ^ N) {r : A} (hr : r ^ N = r) : ∃ c : K, algebraMap K A c = r := by
  -- `X ^ N - X` splits over `K`
  set P : K[X] := X ^ N - X with hP
  have hPm : P.Monic := monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hN)
  have hPdeg : P.natDegree = N := by
    rw [hP, natDegree_sub_eq_left_of_natDegree_lt] <;> simp; omega
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm
    IsAlgClosed.card_roots_eq_natDegree
  have h0 : (P.roots.map fun c ↦ r - algebraMap K A c).prod ∈ maximalIdeal A := by
    have := congr(aeval r $hprod)
    rw [map_multiset_prod, Multiset.map_map] at this
    simp only [Function.comp_def, map_sub, aeval_X, aeval_C, hP, map_pow, hr, sub_self] at this
    rw [this]
    exact zero_mem _
  obtain ⟨_, hmem, hn⟩ := ((maximalIdeal.isMaximal A).isPrime.multiset_prod_mem_iff_exists_mem
    _).mp h0
  obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hmem
  have hcN : c ^ N = c := by
    have := (mem_roots hPm.ne_zero).mp hc
    simpa [hP, sub_eq_zero] using this
  refine ⟨c, ?_⟩
  -- `n = r - c` lies in `𝔪` and satisfies `n ^ N = n`
  set n := r - algebraMap K A c
  have hnN : n ^ N = n := by
    rw [← hχ, map_sub, hχ, hχ, hr, ← map_pow, hcN]
  have hunit : IsUnit (1 - n ^ (N - 1)) := by
    refine (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ?_)
    exact (maximalIdeal A).pow_mem_of_mem hn _ (by omega)
  have : n * (1 - n ^ (N - 1)) = 0 := by
    rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega), hnN, sub_self]
  have hn0 : n = 0 := by
    simpa using (hunit.mul_left_eq_zero).mp this
  exact (sub_eq_zero.mp hn0).symm

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {k : Type u} [Field k] [IsAlgClosed k]
  {S X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)} {a : S ⟶ Spec (.of k)} {p : S ⟶ X₀}
  {σ : Spec (.of k) ⟶ Spec (.of k₀)}

/-- **A local point fixed by a lift of a Frobenius is constant** (blueprint
`thm-trf-frobenius-fixed-points`, the fixed scheme is reduced): let `S = X₀ ×_{k₀} k` with `k`
algebraically closed, let `h` be a `k`-endomorphism of `S` with `h ≫ p = p ≫ G` for a
`#k₀ ^ m`-power Frobenius `G` of `X₀`, `m ≥ 1`, and let `t : Spec A ⟶ S` be a point with values
in a local ring fixed by `h`. Then `t` factors through a `k`-rational point `x` of `S` fixed by
`h`, along the structure morphism `Spec A ⟶ Spec k`. -/
theorem exists_eq_comp_of_comp_eq_self_of_isFrobenius (hp : IsPullback p a f₀ σ)
    {G : X₀ ⟶ X₀} {m : ℕ} (hm : 1 ≤ m) (hG : G.IsFrobenius (Nat.card k₀ ^ m)) {h : S ⟶ S}
    (ha : h ≫ a = a) (hh : h ≫ p = p ≫ G) {A : CommRingCat.{u}} [IsLocalRing A]
    (t : Spec A ⟶ S) (ht : t ≫ h = t) :
    ∃ x : Spec (.of k) ⟶ S, x ≫ a = 𝟙 _ ∧ x ≫ h = x ∧ t = t ≫ a ≫ x := by
  have hN : 2 ≤ Nat.card k₀ ^ m :=
    (Nat.le_self_pow (by omega) _).trans' (Finite.one_lt_card (α := k₀))
  -- the structure map `ι : k ⟶ A`
  let ι : CommRingCat.of k ⟶ A := Spec.preimage (t ≫ a)
  have hι : Spec.map ι = t ≫ a := Spec.map_preimage _
  let _ : Algebra k A := ι.hom.toAlgebra
  have hιinj : Function.Injective ι.hom := ι.hom.injective
  -- the point `t₀ = t ≫ p` of `X₀` is fixed by the Frobenius of `A`
  let t₀ := t ≫ p
  obtain ⟨χ, hχ⟩ := exists_ringHom_pow_card_pow (t₀ ≫ f₀) m
  have hfix : Spec.map χ ≫ t₀ = t₀ := by
    rw [← hG t₀ χ hχ]
    change (t ≫ p) ≫ G = t ≫ p
    rw [Category.assoc, ← hh, ← Category.assoc, ht]
  have : IsLocalHom χ.hom := ⟨fun r hr ↦ by
    rw [hχ] at hr
    exact (isUnit_pow_iff (by omega)).mp hr⟩
  -- its stalk map `φ₀ : 𝒪_{X₀, y₀} ⟶ A`
  let y₀ := t₀ (closedPoint A)
  let φ₀ : X₀.presheaf.stalk y₀ ⟶ A := Scheme.stalkClosedPointTo t₀
  have hφ₀ : Spec.map φ₀ ≫ X₀.fromSpecStalk y₀ = t₀ :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk t₀
  have : IsLocalHom (φ₀ ≫ χ).hom := by
    rw [CommRingCat.hom_comp]
    infer_instance
  have hφχ : φ₀ ≫ χ = φ₀ := by
    have h₁ := (SpecToEquivOfLocalRing X₀ A).symm.injective
      (a₁ := ⟨y₀, φ₀ ≫ χ, inferInstance⟩) (a₂ := ⟨y₀, φ₀, inferInstance⟩) (by
        simp only [SpecToEquivOfLocalRing_symm_apply, Spec.map_comp, Category.assoc, hφ₀]
        exact hfix)
    simpa using h₁
  have hpow (s : X₀.presheaf.stalk y₀) : φ₀ s ^ Nat.card k₀ ^ m = φ₀ s := by
    rw [← hχ, ← CommRingCat.comp_apply, hφχ]
  -- `φ₀` takes values in `k`
  choose c hc using fun s ↦
    IsLocalRing.exists_algebraMap_eq_of_pow_eq_self (K := k) hN χ.hom hχ (hpow s)
  have hc' (s) : ι (c s) = φ₀ s := hc s
  let φ' : X₀.presheaf.stalk y₀ →+* k :=
    { toFun := c
      map_one' := hιinj (by rw [hc', map_one, map_one])
      map_mul' := fun s s' ↦ hιinj (by rw [hc', map_mul, map_mul, hc', hc'])
      map_zero' := hιinj (by rw [hc', map_zero, map_zero])
      map_add' := fun s s' ↦ hιinj (by rw [hc', map_add, map_add, hc', hc']) }
  have hφ' : CommRingCat.ofHom φ' ≫ ι = φ₀ := by
    ext s
    exact hc' s
  have hcN (s) : c s ^ Nat.card k₀ ^ m = c s :=
    hιinj (by rw [map_pow, hc', hpow])
  -- the rational point `x₀ : Spec k ⟶ X₀`
  let x₀ := Spec.map (CommRingCat.ofHom φ') ≫ X₀.fromSpecStalk y₀
  have ht₀ : Spec.map ι ≫ x₀ = t₀ := by
    rw [← Category.assoc, ← Spec.map_comp, hφ', hφ₀]
  have hx₀ : x₀ ≫ f₀ = σ := by
    have h₁ : Spec.map ι ≫ x₀ ≫ f₀ = Spec.map ι ≫ σ := by
      rw [← Category.assoc, ht₀, hι, Category.assoc, Category.assoc, ← hp.w]
    rw [← Spec.map_preimage (x₀ ≫ f₀), ← Spec.map_preimage σ] at h₁ ⊢
    rw [← Spec.map_comp, ← Spec.map_comp] at h₁
    congr 1
    ext r
    exact hιinj congr(($(Spec.map_injective h₁)).hom r)
  let x : Spec (.of k) ⟶ S := hp.lift x₀ (𝟙 _) (by rw [hx₀, Category.id_comp])
  have hxp : x ≫ p = x₀ := hp.lift_fst _ _ _
  have hxa : x ≫ a = 𝟙 _ := hp.lift_snd _ _ _
  refine ⟨x, hxa, ?_, ?_⟩
  · refine hp.hom_ext ?_ (by rw [Category.assoc, ha])
    obtain ⟨χk, hχk⟩ := exists_ringHom_pow_card_pow (x₀ ≫ f₀) m
    have hφχk : CommRingCat.ofHom φ' ≫ χk = CommRingCat.ofHom φ' := by
      ext s
      change χk (c s) = c s
      rw [hχk, hcN]
    rw [Category.assoc, hh, ← Category.assoc, hxp, hG x₀ χk hχk, ← Category.assoc,
      ← Spec.map_comp, hφχk]
  · refine hp.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hxp, ← Category.assoc, ← hι, ht₀]
    · rw [Category.assoc, Category.assoc, hxa, Category.comp_id]

end AlgebraicGeometry
