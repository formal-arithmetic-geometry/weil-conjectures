/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Local injectivity on closed points of finite algebras over w-strictly-local rings

Let `A` be a w-strictly-local ring and `B` a module-finite `A`-algebra. We show that the map
`Spec B → Spec A` is locally injective on closed points: every maximal ideal `x` of `B` has a
basic open neighbourhood `D(s)` such that distinct maximal ideals of `B` in `D(s)` have distinct
images in `Spec A`.

The residue fields of `B` at maximal ideals are purely inseparable over the separably closed
residue fields of `A`, so a prime of `B ⊗[A] B` over a pair `(x, x)` contains the kernel of
multiplication. Since `Spec A` is w-local, the primes of `B ⊗[A] B` over closed points of `Spec A`
are maximal, and a localization argument spreads this out to a neighbourhood of `x`.

## Main results

- `PrimeSpectrum.exists_comap_tensorProduct_eq`: a pair of primes of `S` and `T` over the same
  prime of `R` comes from a prime of `S ⊗[R] T`.
- `IsWStrictlyLocalRing.exists_injOn_closedPoints`: the local injectivity statement.
-/

@[expose] public section

universe u

open PrimeSpectrum Algebra.TensorProduct TensorProduct

/-- Primes `p` of `S` and `q` of `T` with the same contraction to `R` are the contractions of a
prime of `S ⊗[R] T`. -/
lemma PrimeSpectrum.exists_comap_tensorProduct_eq {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] (p : PrimeSpectrum S) (q : PrimeSpectrum T)
    (h : comap (algebraMap R S) p = comap (algebraMap R T) q) :
    ∃ Q : PrimeSpectrum (S ⊗[R] T), comap includeLeftRingHom Q = p ∧
      comap (includeRight : T →ₐ[R] S ⊗[R] T).toRingHom Q = q :=
  AlgebraicGeometry.Scheme.exists_preimage_of_isPullback
    (AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct R S T)) p q h

namespace IsWStrictlyLocalRing

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Let `x` be a maximal ideal of an integral algebra `B` over a w-strictly-local ring `A`, and
`Q` a prime of `B ⊗[A] B` whose two contractions to `B` are `x`. Then `Q` contains
`b ⊗ 1 - 1 ⊗ b` for every `b`: the two induced embeddings of `B ⧸ x` into `(B ⊗[A] B) ⧸ Q` agree
on the separably closed field `A ⧸ (x ∩ A)`, over which `B ⧸ x` is purely inseparable. -/
lemma tmul_one_sub_one_tmul_mem [IsWStrictlyLocalRing A] [Algebra.IsIntegral A B]
    (x : Ideal B) [x.IsMaximal] (Q : Ideal (B ⊗[A] B)) [Q.IsPrime]
    (h₁ : Q.comap includeLeftRingHom = x)
    (h₂ : Q.comap (includeRight : B →ₐ[A] B ⊗[A] B).toRingHom = x) (b : B) :
    b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ b ∈ Q := by
  set m := x.comap (algebraMap A B)
  have : m.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal x
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let : Field (B ⧸ x) := Ideal.Quotient.field x
  have := IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization m
  have : IsSepClosed (A ⧸ m) := IsSepClosed.of_ringEquiv
    (RingEquiv.ofBijective _ m.bijective_algebraMap_quotient_residueField).symm
  let j₁ : B ⧸ x →+* (B ⊗[A] B) ⧸ Q :=
    Ideal.Quotient.lift x ((Ideal.Quotient.mk Q).comp includeLeftRingHom) fun c hc ↦ by
      rw [← h₁] at hc
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_comap.1 hc)
  let j₂ : B ⧸ x →+* (B ⊗[A] B) ⧸ Q :=
    Ideal.Quotient.lift x ((Ideal.Quotient.mk Q).comp
      (includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) fun c hc ↦ by
      rw [← h₂] at hc
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_comap.1 hc)
  have heq : j₁.comp (algebraMap (A ⧸ m) (B ⧸ x)) = j₂.comp (algebraMap (A ⧸ m) (B ⧸ x)) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_)
    change j₁ (Ideal.Quotient.mk x (algebraMap A B a)) = j₂ (Ideal.Quotient.mk x (algebraMap A B a))
    simp only [Ideal.Quotient.lift_mk, j₁, j₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, includeLeftRingHom_apply, includeRight_apply]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, smul_tmul]
  have hj := congrArg (fun f ↦ f (Ideal.Quotient.mk x b))
    (IsPurelyInseparable.injective_comp_algebraMap (A ⧸ m) (B ⧸ x) ((B ⊗[A] B) ⧸ Q) heq)
  simp only [j₁, j₂, Ideal.Quotient.lift_mk, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, includeLeftRingHom_apply, includeRight_apply] at hj
  exact Ideal.Quotient.eq.1 hj

/-- Let `x` be a maximal ideal of an integral algebra `B` over a w-strictly-local ring `A`, and
`Q` a prime of `B ⊗[A] B` lying over a closed point of `Spec A` and containing no `s ⊗ s` with
`s ∉ x`. Then `Q` contains `b ⊗ 1 - 1 ⊗ b` for every `b`: both contractions of `Q` to `B` are
contained in `x` and lie over a closed point, hence are equal to `x`. -/
lemma tmul_one_sub_one_tmul_mem_of_forall_not_mem [IsWStrictlyLocalRing A]
    [Algebra.IsIntegral A B] (x : Ideal B) [x.IsMaximal] (Q : Ideal (B ⊗[A] B)) [Q.IsPrime]
    (hI : (vanishingIdeal (closedPoints (PrimeSpectrum A))).map (algebraMap A (B ⊗[A] B)) ≤ Q)
    (hQ : ∀ s ∉ x, s ⊗ₜ[A] s ∉ Q) (b : B) : b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ b ∈ Q := by
  have hss (s : B) : s ⊗ₜ[A] s = (s ⊗ₜ[A] (1 : B)) * (1 ⊗ₜ s) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hle₁ : Q.comap includeLeftRingHom ≤ x := fun c hc ↦ by
    by_contra hcx
    exact hQ c hcx (hss c ▸ Q.mul_mem_right _ hc)
  have hle₂ : Q.comap (includeRight : B →ₐ[A] B ⊗[A] B).toRingHom ≤ x := fun c hc ↦ by
    by_contra hcx
    exact hQ c hcx (hss c ▸ Q.mul_mem_left _ hc)
  have hp : (Q.comap (algebraMap A (B ⊗[A] B))).IsMaximal := by
    have h₁ : vanishingIdeal (closedPoints (PrimeSpectrum A)) ≤
        Q.comap (algebraMap A (B ⊗[A] B)) := Ideal.map_le_iff_le_comap.1 hI
    have h₂ : (⟨Q.comap (algebraMap A (B ⊗[A] B)), Ideal.comap_isPrime _ Q⟩ : PrimeSpectrum A) ∈
        closure (closedPoints (PrimeSpectrum A)) := by
      rw [← zeroLocus_vanishingIdeal_eq_closure, mem_zeroLocus]
      exact h₁
    rw [WLocalSpace.isClosed_closedPoints.closure_eq] at h₂
    exact (isClosed_singleton_iff_isMaximal _).1 h₂
  have e₁ : Q.comap includeLeftRingHom = x := by
    have : ((Q.comap includeLeftRingHom).comap (algebraMap A B)).IsMaximal := by
      rwa [Ideal.comap_comap]
    exact (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ this).eq_of_le
      Ideal.IsPrime.ne_top' hle₁
  have e₂ : Q.comap (includeRight : B →ₐ[A] B ⊗[A] B).toRingHom = x := by
    have : ((Q.comap (includeRight : B →ₐ[A] B ⊗[A] B).toRingHom).comap
        (algebraMap A B)).IsMaximal := by
      rwa [Ideal.comap_comap, ← includeLeftRingHom_comp_algebraMap]
    exact (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ this).eq_of_le
      Ideal.IsPrime.ne_top' hle₂
  exact tmul_one_sub_one_tmul_mem x Q e₁ e₂ b

/-- Let `x` be a maximal ideal of an integral algebra `B` over a w-strictly-local ring `A`. For
every `b : B` there are `s ∉ x` and `n` such that `(s ⊗ s) (b ⊗ 1 - 1 ⊗ b) ^ n` lies in the
ideal of `B ⊗[A] B` generated by the functions vanishing on the closed points of `Spec A`.

Otherwise a prime ideal containing this ideal and avoiding the multiplicative set generated by
the `s ⊗ s` and `b ⊗ 1 - 1 ⊗ b` would contradict
`IsWStrictlyLocalRing.tmul_one_sub_one_tmul_mem_of_forall_not_mem`. -/
lemma exists_mul_pow_mem [IsWStrictlyLocalRing A] [Algebra.IsIntegral A B] (x : Ideal B)
    [x.IsMaximal] (b : B) :
    ∃ s ∉ x, ∃ n : ℕ, (s ⊗ₜ[A] s) * (b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ b) ^ n ∈
      (vanishingIdeal (closedPoints (PrimeSpectrum A))).map (algebraMap A (B ⊗[A] B)) := by
  by_contra! H
  let D : B →* B ⊗[A] B := (includeLeftRingHom : B →+* B ⊗[A] B).toMonoidHom *
    ((includeRight : B →ₐ[A] B ⊗[A] B) : B →+* B ⊗[A] B).toMonoidHom
  have hD (s : B) : D s = s ⊗ₜ[A] s := by
    simp [D, Algebra.TensorProduct.tmul_mul_tmul]
  let M : Submonoid (B ⊗[A] B) :=
    x.primeCompl.map D ⊔ Submonoid.powers (b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ b)
  have hdisj : Disjoint ((vanishingIdeal (closedPoints (PrimeSpectrum A))).map
      (algebraMap A (B ⊗[A] B)) : Set (B ⊗[A] B)) M := by
    rw [Set.disjoint_right]
    intro y hy hyI
    obtain ⟨u, hu, v, hv, rfl⟩ := Submonoid.mem_sup.1 hy
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.1 hu
    obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 hv
    exact H s hs n (by rwa [← hD])
  obtain ⟨Q, hQ, hIQ, hQM⟩ := Ideal.exists_le_prime_disjoint _ M hdisj
  refine Set.disjoint_left.1 hQM (tmul_one_sub_one_tmul_mem_of_forall_not_mem x Q hIQ ?_ b)
    (Submonoid.mem_sup_right (Submonoid.mem_powers _))
  intro s hs hsQ
  exact Set.disjoint_left.1 hQM hsQ (Submonoid.mem_sup_left ⟨s, hs, hD s⟩)

/-- **Local injectivity on closed points.** Let `B` be a module-finite algebra over a
w-strictly-local ring `A` and `x` a maximal ideal of `B`. There is `s ∉ x` such that two maximal
ideals of `B` not containing `s` and with the same contraction to `A` are equal.

With `s` the product of the elements provided by `IsWStrictlyLocalRing.exists_mul_pow_mem` for
a finite set of `A`-module generators `c` of `B`, a prime `Q` of `B ⊗[A] B` over two such maximal
ideals contains all `c ⊗ 1 - 1 ⊗ c`, hence all `b ⊗ 1 - 1 ⊗ b`. -/
theorem exists_injOn_closedPoints [IsWStrictlyLocalRing A] [Module.Finite A B] (x : Ideal B)
    [x.IsMaximal] :
    ∃ s ∉ x, ∀ q₁ q₂ : PrimeSpectrum B, q₁.asIdeal.IsMaximal → q₂.asIdeal.IsMaximal →
      s ∉ q₁.asIdeal → s ∉ q₂.asIdeal →
        comap (algebraMap A B) q₁ = comap (algebraMap A B) q₂ → q₁ = q₂ := by
  classical
  obtain ⟨g, hg⟩ := Module.Finite.fg_top (R := A) (M := B)
  choose! t ht n hn using fun c ↦ exists_mul_pow_mem (A := A) x c
  refine ⟨∏ c ∈ g, t c, fun h ↦ ?_, fun q₁ q₂ h₁ h₂ hs₁ hs₂ hq ↦ ?_⟩
  · obtain ⟨c, -, hc⟩ := (Ideal.IsPrime.prod_mem_iff (hp := inferInstance)).1 h
    exact ht c hc
  obtain ⟨Q, hQ₁, hQ₂⟩ := PrimeSpectrum.exists_comap_tensorProduct_eq q₁ q₂ hq
  have hQA : comap (algebraMap A (B ⊗[A] B)) Q = comap (algebraMap A B) q₁ := by
    rw [← hQ₁, ← comap_comp_apply]
    rfl
  have hIQ : (vanishingIdeal (closedPoints (PrimeSpectrum A))).map
      (algebraMap A (B ⊗[A] B)) ≤ Q.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [mem_vanishingIdeal] at ha
    have hmax : comap (algebraMap A B) q₁ ∈ closedPoints (PrimeSpectrum A) := by
      rw [mem_closedPoints_iff, isClosed_singleton_iff_isMaximal]
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q₁.asIdeal
    have := ha _ hmax
    rw [← hQA] at this
    exact this
  have hnot (c : B) (hc : c ∈ g) (q : PrimeSpectrum B) (hsq : ∏ c ∈ g, t c ∉ q.asIdeal) :
      t c ∉ q.asIdeal := fun h ↦ hsq (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem t hc) h)
  have hδ (c : B) (hc : c ∈ g) : c ⊗ₜ[A] (1 : B) - 1 ⊗ₜ c ∈ Q.asIdeal := by
    rcases Q.isPrime.mem_or_mem (hIQ (hn c)) with h | h
    · exfalso
      have hss : t c ⊗ₜ[A] t c = (t c ⊗ₜ[A] (1 : B)) * (1 ⊗ₜ t c) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hss] at h
      rcases Q.isPrime.mem_or_mem h with h | h
      · exact hnot c hc q₁ hs₁ (by rw [← hQ₁]; exact h)
      · exact hnot c hc q₂ hs₂ (by rw [← hQ₂]; exact h)
    · exact Q.isPrime.mem_of_pow_mem _ h
  have hall (b : B) : b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ b ∈ Q.asIdeal := by
    have hb : b ∈ Submodule.span A (g : Set B) := hg ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem c hc => exact hδ c hc
    | zero => simp
    | add c d _ _ hc hd =>
      convert Q.asIdeal.add_mem hc hd using 1
      rw [add_tmul, tmul_add]
      abel
    | smul a c _ hc =>
      convert Q.asIdeal.mul_mem_left (algebraMap A (B ⊗[A] B) a) hc using 1
      rw [← Algebra.smul_def, smul_sub, smul_tmul', smul_tmul', ← smul_tmul]
  ext1
  rw [← hQ₁, ← hQ₂]
  ext b
  simp only [comap_asIdeal, Ideal.mem_comap, includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, includeRight_apply]
  constructor
  · intro h
    simpa using Q.asIdeal.sub_mem h (hall b)
  · intro h
    simpa using Q.asIdeal.add_mem h (hall b)

end IsWStrictlyLocalRing
