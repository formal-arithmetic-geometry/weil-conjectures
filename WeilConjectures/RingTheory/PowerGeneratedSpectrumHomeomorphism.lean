/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.RingTheory.PrimePowerAdditionSubring
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra

/-!
# Power-generated ring maps induce universal homeomorphisms

Source: Stacks Project, Algebra, Tag 0BRA, lemma-p-ring-map
(blueprint: lem-pur-power-generated-spectrum-homeomorphism).
-/

@[expose] public section

universe u v

open TensorProduct

namespace AlgebraicGeometry

private theorem power_conditions_of_adjoin
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (p : ℕ) (hp : p.Prime) (s : Set B) (hgen : Algebra.adjoin R s = ⊤)
    (hpow : ∀ x ∈ s, ∃ n : ℕ, 0 < n ∧
      x ^ (p ^ n) ∈ (algebraMap R B).range ∧
      (p ^ n : B) * x ∈ (algebraMap R B).range) (x : B) :
    ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ (algebraMap R B).range ∧
      (p ^ n : B) * x ∈ (algebraMap R B).range := by
  have hx : x ∈ Algebra.adjoin R s := hgen ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact hpow x hx
  | algebraMap r =>
    refine ⟨1, by omega, ⟨r ^ p, by simp⟩, ⟨(p : R) * r, by simp⟩⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨n, hn, hxn, hpx⟩ := ihx
    obtain ⟨m, hm, hym, hpy⟩ := ihy
    simpa only [Nat.cast_pow] using
      (algebraMap R B).range.exists_prime_pow_add_mem hp hn hm hxn hpx hym hpy
  | mul x y hx hy ihx ihy =>
    obtain ⟨n, hn, hxn, hpx⟩ := ihx
    obtain ⟨m, hm, hym, hpy⟩ := ihy
    refine ⟨n + m, by omega, ?_, ?_⟩
    · convert (algebraMap R B).range.mul_mem
        ((algebraMap R B).range.pow_mem hxn (p ^ m))
        ((algebraMap R B).range.pow_mem hym (p ^ n)) using 1
      rw [mul_pow, pow_add, pow_mul, pow_mul]
      congr 1
      rw [← pow_mul, ← pow_mul, mul_comm (p ^ n) (p ^ m)]
    · convert (algebraMap R B).range.mul_mem hpx hpy using 1
      rw [pow_add]
      ring

private theorem field_hom_ext_of_power_conditions
    {R B K : Type*} [CommRing R] [CommRing B] [Algebra R B] [Field K]
    (p : ℕ) (hp : p.Prime)
    (hpow : ∀ x : B, ∃ n : ℕ, 0 < n ∧
      x ^ (p ^ n) ∈ (algebraMap R B).range ∧
      (p ^ n : B) * x ∈ (algebraMap R B).range)
    (f g : B →+* K) (h : f.comp (algebraMap R B) = g.comp (algebraMap R B)) : f = g := by
  have hr (r : R) : f (algebraMap R B r) = g (algebraMap R B r) :=
    RingHom.congr_fun h r
  ext x
  obtain ⟨n, hn, ⟨r, hrx⟩, ⟨t, htx⟩⟩ := hpow x
  by_cases hpc : (p : K) = 0
  · have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := (CharP.charP_iff_prime_eq_zero hp).mpr hpc
    apply iterateFrobenius_inj K p n
    change f x ^ (p ^ n) = g x ^ (p ^ n)
    simpa only [← map_pow, ← hrx] using hr r
  · apply mul_left_cancel₀ (pow_ne_zero n hpc)
    have ht := hr t
    rw [htx] at ht
    simpa only [map_mul, map_pow, map_natCast] using ht

private theorem isUniversalHomeomorphism_of_power_conditions
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (p : ℕ) (hp : p.Prime)
    (hker : ∀ r : R, algebraMap R B r = 0 → IsNilpotent r)
    (hpow : ∀ x : B, ∃ n : ℕ, 0 < n ∧
      x ^ (p ^ n) ∈ (algebraMap R B).range ∧
      (p ^ n : B) * x ∈ (algebraMap R B).range) :
    Algebra.IsUniversalHomeomorphism R B := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have hpowers (x : B) : ∃ n > 0, x ^ n ∈ (algebraMap R B).range := by
    obtain ⟨n, hn, hxn, hpx⟩ := hpow x
    exact ⟨p ^ n, pow_pos hp.pos n, hxn⟩
  have hnil : RingHom.ker (algebraMap R B) ≤ nilradical R := by
    intro r hr
    exact mem_nilradical.mpr (hker r hr)
  have : Algebra.IsIntegral R B := ⟨fun x ↦ by
    obtain ⟨n, hn, r, hr⟩ := hpowers x
    exact IsIntegral.of_pow hn (hr ▸ isIntegral_algebraMap)⟩
  have : IsIntegralHom f := IsIntegralHom.SpecMap_iff.mpr
    ((algebraMap_isIntegral_iff (R := R) (A := B)).mpr inferInstance)
  have : Surjective f := ⟨(PrimeSpectrum.isHomeomorph_comap _ hpowers hnil).surjective⟩
  have : UniversallyInjective f := by
    refine ((tfae_universallyInjective f).out 1 0).mp ?_
    intro K _ g₁ g₂ hg
    rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂] at hg ⊢
    simp only [f, ← Spec.map_comp] at hg
    have h := Spec.map_injective hg
    congr 1
    apply CommRingCat.hom_ext
    exact field_hom_ext_of_power_conditions p hp hpow _ _
      (congrArg CommRingCat.Hom.hom h)
  exact ⟨{ }⟩

private theorem nil_kernel_tensor_of_power_conditions
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (p : ℕ) (hp : p.Prime)
    (hker : ∀ r : R, algebraMap R B r = 0 → IsNilpotent r)
    (hpow : ∀ x : B, ∃ n : ℕ, 0 < n ∧
      x ^ (p ^ n) ∈ (algebraMap R B).range ∧
      (p ^ n : B) * x ∈ (algebraMap R B).range)
    (A : Type v) [CommRing A] [Algebra R A]
    (r : A) (hr : algebraMap A (A ⊗[R] B) r = 0) : IsNilpotent r := by
  let R₀ := ULift.{v} R
  let B₀ := ULift.{v} B
  let A₀ := ULift.{u} A
  let : Algebra R₀ B₀ := ULift.algebra' R B₀
  let : Algebra R₀ A₀ := ULift.algebra' R A₀
  have hker₀ (r : R₀) (hr : algebraMap R₀ B₀ r = 0) : IsNilpotent r := by
    exact (hker r.down (congrArg ULift.down hr)).map
      (ULift.ringEquiv : R₀ ≃+* R).symm.toRingHom
  have hpow₀ (x : B₀) : ∃ n : ℕ, 0 < n ∧
      x ^ (p ^ n) ∈ (algebraMap R₀ B₀).range ∧
      (p ^ n : B₀) * x ∈ (algebraMap R₀ B₀).range := by
    obtain ⟨n, hn, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hpow x.down
    exact ⟨n, hn, ⟨ULift.up a, congrArg ULift.up ha⟩,
      ⟨ULift.up b, congrArg ULift.up hb⟩⟩
  have : Algebra.IsUniversalHomeomorphism R₀ B₀ :=
    isUniversalHomeomorphism_of_power_conditions p hp hker₀ hpow₀
  have hsurj := Algebra.IsUniversalHomeomorphism.comap_surjective A₀ (A₀ ⊗[R₀] B₀)
  have hnil : RingHom.ker (algebraMap A₀ (A₀ ⊗[R₀] B₀)) ≤ nilradical A₀ :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mp hsurj.denseRange
  have hz : algebraMap A₀ (A₀ ⊗[R₀] B₀) (ULift.up r) = 0 := by
    let e : ULift.{0} (A ⊗[R] B) ≃ₐ[A] A₀ ⊗[R₀] B₀ :=
      Algebra.TensorProduct.uliftEquiv R A A B
    have hh := congrArg (fun x ↦ e (ULift.up x)) hr
    change (ULift.up r : A₀) ⊗ₜ[R₀] (1 : B₀) = e 0 at hh
    simpa only [Algebra.TensorProduct.algebraMap_apply, ULift.algebraMap_apply',
      ULift.algebraMap_eq, Algebra.algebraMap_self, RingHom.id_apply, map_zero] using hh
  exact (mem_nilradical.mp (hnil hz)).map (ULift.ringEquiv : A₀ ≃+* A).toRingHom

/-- A ring map with nil kernel generated by elements whose prime power and prime multiple
belong to its image induces a universal homeomorphism. Every algebra base change retains
both hypotheses and induces a homeomorphism on prime spectra.
Source: Stacks Project, Algebra, Tag 0BRA, lemma-p-ring-map
(blueprint: lem-pur-power-generated-spectrum-homeomorphism).

Proof plan: Let `T` consist of elements with the two power conditions. The image of the
base ring lies in `T`; negatives and products preserve `T` by the explicit power formulas.
The addition lemma `lem-pur-prime-power-addition-subring` proves closure under sums. Thus
`T` is a subalgebra containing the generators, so it is the whole algebra. Apply
`lem-pur-all-element-powers-spectrum-homeomorphism` to the nil kernel and these powers.
For any base change, identify spectra of tensor products with affine fibre products using
`lem-weil-pbc-fibre-product-affine-spectra`. Spectrum surjectivity survives base change by
`lem-weil-pbc-surjective-base-change`; hence the new kernel lies in every prime and is nil
by `lem-weil-pbc-zero-locus-eq-iff-radical-eq`. The tensors `1 ⊗ x` generate the new algebra
by `lem-weil-pbc-algebra-tensor-pushout-universal-property`; balancing preserves both power
conditions. Repeat the subalgebra argument and the all-element power criterion. Finally,
cover an arbitrary scheme base change by affine opens: the projection is a homeomorphism
on each chart, and these homeomorphisms glue, including for the empty scheme. This is the
universal property `def-weil-universal-homeomorphism`. -/
theorem universally_isHomeomorph_specMap_of_power_generated
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (p : ℕ) (hp : p.Prime)
    (hker : ∀ r : R, algebraMap R B r = 0 → IsNilpotent r)
    (s : Set B) (hgen : Algebra.adjoin R s = ⊤)
    (hpow : ∀ x ∈ s, ∃ n : ℕ, 0 < n ∧
      x ^ (p ^ n) ∈ (algebraMap R B).range ∧
      (p ^ n : B) * x ∈ (algebraMap R B).range) :
    (topologically IsHomeomorph).universally
        (Spec.map (CommRingCat.ofHom (algebraMap R B))) ∧
      ∀ (R' : Type (max u v)) [CommRing R'] [Algebra R R'],
        (∀ r : R', algebraMap R' (R' ⊗[R] B) r = 0 → IsNilpotent r) ∧
        (∃ s' : Set (R' ⊗[R] B), Algebra.adjoin R' s' = ⊤ ∧
          ∀ x ∈ s', ∃ n : ℕ, 0 < n ∧
            x ^ (p ^ n) ∈ (algebraMap R' (R' ⊗[R] B)).range ∧
            (p ^ n : R' ⊗[R] B) * x ∈ (algebraMap R' (R' ⊗[R] B)).range) ∧
        IsHomeomorph (PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] B))) := by
  have hAll := power_conditions_of_adjoin p hp s hgen hpow
  have hUH := isUniversalHomeomorphism_of_power_conditions p hp hker hAll
  refine ⟨@isUniversalHomeomorphism_le_universally_isHomeomorph _ _ _
    hUH.isUniversalHomeomorphism, ?_⟩
  intro R' _ _
  let s' : Set (R' ⊗[R] B) := ((1 : R') ⊗ₜ[R] ·) '' s
  have hgen' : Algebra.adjoin R' s' = ⊤ :=
    Algebra.TensorProduct.adjoin_one_tmul_image_eq_top s hgen
  have hpow' : ∀ x ∈ s', ∃ n : ℕ, 0 < n ∧
      x ^ (p ^ n) ∈ (algebraMap R' (R' ⊗[R] B)).range ∧
      (p ^ n : R' ⊗[R] B) * x ∈ (algebraMap R' (R' ⊗[R] B)).range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn, ⟨r, hr⟩, ⟨t, ht⟩⟩ := hpow x hx
    refine ⟨n, hn, ⟨algebraMap R R' r, ?_⟩, ⟨algebraMap R R' t, ?_⟩⟩
    · rw [Algebra.TensorProduct.tmul_pow, one_pow, ← hr]
      exact (Algebra.TensorProduct.includeRight (A := R')).commutes r |>.symm
    · have h := (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := B)).commutes t
      rw [ht] at h
      rw [← IsScalarTower.algebraMap_apply R R' (R' ⊗[R] B)]
      simpa only [map_mul, map_pow, map_natCast,
        Algebra.TensorProduct.includeRight_apply] using h.symm
  have hker' := nil_kernel_tensor_of_power_conditions p hp hker hAll R'
  refine ⟨hker', ⟨s', hgen', hpow'⟩, ?_⟩
  apply PrimeSpectrum.isHomeomorph_comap
  · intro x
    obtain ⟨n, hn, hxn, hpx⟩ := power_conditions_of_adjoin p hp s' hgen' hpow' x
    exact ⟨p ^ n, pow_pos hp.pos n, hxn⟩
  · intro r hr
    exact mem_nilradical.mpr (hker' r hr)

end AlgebraicGeometry
