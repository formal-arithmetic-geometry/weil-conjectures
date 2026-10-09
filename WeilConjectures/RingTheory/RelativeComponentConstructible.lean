/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.RingTheory.GenericConnectedness
public import WeilConjectures.Mathlib.Topology.NoetherianSpace

/-!
# Constructibility of the relative connected component over a noetherian base

Let `A` be a noetherian ring and `B` a finite type `A`-algebra with an `A`-valued point
`s : B →ₐ[A] A`. For a prime `q` of `B` lying over `p`, the fibre of `Spec B → Spec A` over `p`
contains the point `s⁻¹ p` given by the section. The set of primes `q` lying in the connected
component of `s⁻¹ p` in their fibre is constructible (Stacks `055P`, noetherian case `055N`).

## Main statements

- `PrimeSpectrum.isConstructible_of_forall_exists_basicOpen`: a noetherian induction criterion
  for constructibility of subsets of a space over `Spec A`.
- `PrimeSpectrum.isConstructible_relativeComponent`: the relative component is constructible.

## References

- Stacks Project, Tags `055N` and `055P`
-/

@[expose] public section

universe u

open TensorProduct Topology

namespace PrimeSpectrum

/-- **Noetherian induction over `Spec A`.** Let `A` be noetherian and `φ : X → Spec A`. If for
every prime `p` of `A` there is `a ∉ p` such that the part of `S` lying over `V(p) ∩ D(a)` is
constructible, then `S` is constructible. -/
theorem isConstructible_of_forall_exists_basicOpen {A X : Type*} [CommRing A]
    [IsNoetherianRing A] [TopologicalSpace X] (φ : X → PrimeSpectrum A) (S : Set X)
    (h : ∀ p : PrimeSpectrum A, ∃ a ∉ p.asIdeal,
      IsConstructible (S ∩ φ ⁻¹' (zeroLocus p.asIdeal ∩ basicOpen a))) :
    IsConstructible S := by
  by_contra hS
  obtain ⟨I, hI, hmax⟩ := set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian A A)
    {I : Ideal A | ¬IsConstructible (S ∩ φ ⁻¹' zeroLocus (I : Set A))}
    ⟨⊥, by simpa using hS⟩
  have hlt {x : A} (hx : x ∉ I) :
      IsConstructible (S ∩ φ ⁻¹' zeroLocus ((I ⊔ Ideal.span {x} : Ideal A) : Set A)) := by
    by_contra H
    exact hmax _ H (lt_of_le_of_ne le_sup_left fun e ↦ hx (e ▸ Ideal.mem_sup_right
      (Ideal.mem_span_singleton_self x)))
  have hprime : Ideal.IsPrime (I : Ideal A) := by
    refine Ideal.isPrime_iff.mpr ⟨fun htop ↦ hI ?_, fun {x y} hxy ↦ ?_⟩
    · simp [htop]
    by_contra! hxy'
    refine hI ?_
    convert (hlt hxy'.1).union (hlt hxy'.2) using 1
    rw [← Set.inter_union_distrib_left, ← Set.preimage_union]
    congr 2
    ext q
    simp only [zeroLocus_sup, Set.mem_union, Set.mem_inter_iff, zeroLocus_span,
      mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
    refine ⟨fun hq ↦ ?_, by tauto⟩
    rcases q.isPrime.mem_or_mem (hq (hxy : x * y ∈ I)) with h | h <;> tauto
  obtain ⟨a, ha, hc⟩ := h ⟨I, hprime⟩
  refine hI ?_
  convert hc.union (hlt ha) using 1
  rw [← Set.inter_union_distrib_left, ← Set.preimage_union]
  congr 2
  ext q
  simp only [zeroLocus_sup, Set.mem_union, Set.mem_inter_iff, zeroLocus_span,
    mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe,
    SetLike.mem_coe, mem_basicOpen]
  tauto

end PrimeSpectrum

/-- Let `W = F ∩ V` be a preconnected subset of `F` containing `x`, with `V` closed, which is also
of the form `F ∩ U` with `U` open. Then `W` is the connected component of `x` in `F`. -/
theorem connectedComponentIn_eq_of_inter_eq {X : Type*} [TopologicalSpace X] {F U V : Set X}
    {x : X} (hU : IsOpen U) (hV : IsClosed V) (hUV : F ∩ U = F ∩ V)
    (hW : IsPreconnected (F ∩ V)) (hx : x ∈ F ∩ V) :
    connectedComponentIn F x = F ∩ V := by
  refine subset_antisymm ?_ (hW.subset_connectedComponentIn hx Set.inter_subset_left)
  have hsub := connectedComponentIn_subset F x
  have hcov : connectedComponentIn F x ⊆ U ∪ Vᶜ := by
    intro y hy
    by_cases hyV : y ∈ V
    · exact .inl (hUV ▸ ⟨hsub hy, hyV⟩ : y ∈ F ∩ U).2
    · exact .inr hyV
  have hdisj : connectedComponentIn F x ∩ (U ∩ Vᶜ) = ∅ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
      not_and, not_not]
    intro hy hyU
    exact (hUV ▸ ⟨hsub hy, hyU⟩ : y ∈ F ∩ V).2
  rcases isPreconnected_iff_subset_of_disjoint.mp isPreconnected_connectedComponentIn
    U Vᶜ hU hV.isOpen_compl hcov hdisj with h | h
  · rw [← hUV]
    exact Set.subset_inter hsub h
  · exact absurd hx.2 (h (mem_connectedComponentIn hx.1))

namespace PrimeSpectrum

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- If `y ∈ B` vanishes in the fibre ring `κ(p) ⊗[A] B`, then `y` lies in every prime of `B`
lying over a prime `t ⊇ p` in some open neighbourhood `D(a)` of `p`. -/
theorem exists_forall_mem_of_one_tmul_eq_zero {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (p : PrimeSpectrum A) {y : B}
    (hy : (1 : p.asIdeal.ResidueField) ⊗ₜ[A] y = 0) :
    ∃ a ∉ p.asIdeal, ∀ q : PrimeSpectrum B, p ≤ comap (algebraMap A B) q →
      a ∉ (comap (algebraMap A B) q).asIdeal → y ∈ q.asIdeal := by
  let _ := Algebra.TensorProduct.rightAlgebra (R := A) (A := p.asIdeal.ResidueField) (B := B)
  set M := Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl
  have h0 := congr(Ideal.Fiber.algEquivAux₁ (S := B) p.asIdeal $hy)
  have h1 : (1 : p.asIdeal.ResidueField) ⊗ₜ[A] y = algebraMap B _ y := rfl
  rw [map_zero, h1, AlgEquiv.commutes, IsScalarTower.algebraMap_apply B (Localization M),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem,
    IsLocalization.mem_map_algebraMap_iff M] at h0
  obtain ⟨⟨⟨x, hx⟩, m⟩, h2⟩ := h0
  rw [← map_mul, IsLocalization.eq_iff_exists M] at h2
  obtain ⟨m', h2⟩ := h2
  obtain ⟨a, ha, ha'⟩ := (m' * m).2
  refine ⟨a, ha, fun q hpq haq ↦ ?_⟩
  have hmem : algebraMap A B a * y ∈ q.asIdeal := by
    rw [ha', Submonoid.coe_mul, mul_assoc, mul_comm _ y, h2]
    refine Ideal.mul_mem_left _ _ (Ideal.map_le_iff_le_comap.mpr ?_ hx)
    exact hpq
  exact (q.isPrime.mem_or_mem hmem).resolve_left haq

/-- **The connected component of the section in the fibre over `p`.** Let `B` be a finite type
`A`-algebra with a section `s`, and `p` a prime of `A`. There are `a ∉ p` and `b, c ∈ B` such that
`s c ∈ p`, the part `V(c)` of the fibre over `p` is connected, and over `V(p) ∩ D(a)` every prime
contains `b * c` but not `b - c`; thus `V(c) = D(b)` on those fibres. The set `V(c)` cuts out
the connected component of `s⁻¹ p` in the fibre over `p`, which is clopen as the fibre is
noetherian. -/
theorem exists_isConnected_preimage_inter_zeroLocus [Algebra.FiniteType A B] (s : B →ₐ[A] A)
    (p : PrimeSpectrum A) :
    ∃ a ∉ p.asIdeal, ∃ b c : B, (∀ q : PrimeSpectrum B, p ≤ comap (algebraMap A B) q →
      a ∉ (comap (algebraMap A B) q).asIdeal → b * c ∈ q.asIdeal ∧ b - c ∉ q.asIdeal) ∧
      s c ∈ p.asIdeal ∧ IsConnected (comap (algebraMap A B) ⁻¹' {p} ∩ zeroLocus {c}) := by
  have : IsNoetherianRing (p.asIdeal.Fiber B) :=
    Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField _
  let h := preimageHomeomorphFiber A B p
  have hσ : comap (s : B →+* A) p ∈ comap (algebraMap A B) ⁻¹' {p} := by
    ext x
    simp
  obtain ⟨e, he, hZ⟩ := exists_idempotent_basicOpen_eq_of_isClopen
    (isClopen_connectedComponent (x := h ⟨_, hσ⟩))
  obtain ⟨a₀, ha₀, b, hb⟩ := Ideal.Fiber.exists_smul_eq_one_tmul p.asIdeal e
  set c := b - algebraMap A B a₀
  have hy : (1 : p.asIdeal.ResidueField) ⊗ₜ[A] (b * c) = 0 := by
    have h1 : (1 : p.asIdeal.ResidueField) ⊗ₜ[A] (b * c) =
        Algebra.TensorProduct.includeRight b *
          (Algebra.TensorProduct.includeRight b - algebraMap A (p.asIdeal.Fiber B) a₀) := by
      rw [← AlgHom.commutes Algebra.TensorProduct.includeRight a₀, ← map_sub, ← map_mul]
      rfl
    rw [h1, Algebra.TensorProduct.includeRight_apply, ← hb, Algebra.smul_def]
    linear_combination (algebraMap A (p.asIdeal.Fiber B) a₀) ^ 2 * he.eq
  obtain ⟨a₁, ha₁, H⟩ := exists_forall_mem_of_one_tmul_eq_zero p hy
  have hmem (x : PrimeSpectrum (p.asIdeal.Fiber B)) :
      b ∈ (h.symm x).1.asIdeal ↔ e ∈ x.asIdeal := by
    have hx : algebraMap A _ a₀ ∉ x.asIdeal :=
      fun h' ↦ ha₀ ((Ideal.mem_of_liesOver x.asIdeal p.asIdeal a₀).mpr h')
    rw [← x.isPrime.mul_mem_left_iff hx, ← Algebra.smul_def, hb]
    exact Iff.rfl
  have hfib (q : PrimeSpectrum B) (hq : q ∈ comap (algebraMap A B) ⁻¹' {p}) :
      c ∈ q.asIdeal ↔ b ∉ q.asIdeal := by
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hq
    have hbc := H q hq.ge (by rwa [hq])
    have ha₀q : algebraMap A B a₀ ∉ q.asIdeal := by
      rwa [← Ideal.mem_comap, ← comap_asIdeal, hq]
    refine ⟨fun hc hb ↦ ha₀q ?_, fun hb ↦ (q.isPrime.mem_or_mem hbc).resolve_left hb⟩
    rw [← sub_sub_cancel b (algebraMap A B a₀)]
    exact sub_mem hb hc
  have hset : comap (algebraMap A B) ⁻¹' {p} ∩ zeroLocus {c} =
      Subtype.val '' (h.symm '' connectedComponent (h ⟨_, hσ⟩)) := by
    ext q
    constructor
    · rintro ⟨hq, hcq⟩
      refine ⟨⟨q, hq⟩, ⟨h ⟨q, hq⟩, ?_, by simp⟩, rfl⟩
      rw [hZ, SetLike.mem_coe, mem_basicOpen, ← hmem, Homeomorph.symm_apply_apply]
      exact (hfib q hq).mp (by simpa using hcq)
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [hZ, SetLike.mem_coe, mem_basicOpen, ← hmem] at hx
      refine ⟨(h.symm x).2, ?_⟩
      simpa using (hfib _ (h.symm x).2).mpr hx
  refine ⟨a₀ * a₁, fun h' ↦ (p.isPrime.mem_or_mem h').elim ha₀ ha₁, b, c,
    fun q hpq ha ↦ ⟨H q hpq fun h' ↦ ha (Ideal.mul_mem_left _ _ h'), ?_⟩, ?_, ?_⟩
  · rw [sub_sub_cancel]
    exact fun h' ↦ ha (Ideal.mul_mem_right _ _ h')
  · have hσc : comap (s : B →+* A) p ∈ comap (algebraMap A B) ⁻¹' {p} ∩ zeroLocus {c} := by
      rw [hset]
      exact ⟨⟨_, hσ⟩, ⟨_, mem_connectedComponent, h.symm_apply_apply _⟩, rfl⟩
    simpa using hσc.2
  · rw [hset]
    exact (isConnected_connectedComponent.image _ h.symm.continuous.continuousOn).image _
      continuous_subtype_val.continuousOn

/-- **Spreading out connectedness of a closed piece of the fibres.** Let `A` be noetherian, `B` a
finite type `A`-algebra with a section `s`, `p` a prime of `A` and `c ∈ B` with `s c ∈ p`. If the
part `V(c)` of the fibre over `p` is connected, then so is the part `V(c)` of the fibre over every
`t ⊇ p` in some open neighbourhood `D(a)` of `p`. This is `055G` applied to `B ⧸ (pB + (c))` over
the domain `A ⧸ p`. -/
theorem exists_forall_isPreconnected_preimage_inter_zeroLocus [IsNoetherianRing A]
    [Algebra.FiniteType A B] (s : B →ₐ[A] A) (p : PrimeSpectrum A) (c : B) (hc : s c ∈ p.asIdeal)
    (hconn : IsConnected (comap (algebraMap A B) ⁻¹' {p} ∩ zeroLocus {c})) :
    ∃ a ∉ p.asIdeal, ∀ t : PrimeSpectrum A, p ≤ t → a ∉ t.asIdeal →
      IsPreconnected (comap (algebraMap A B) ⁻¹' {t} ∩ zeroLocus {c}) := by
  set J : Ideal B := p.asIdeal.map (algebraMap A B) ⊔ Ideal.span {c}
  have hpJ : p.asIdeal ≤ J.comap (algebraMap A B) := Ideal.map_le_iff_le_comap.mp le_sup_left
  let _ : Algebra (A ⧸ p.asIdeal) (B ⧸ J) := (Ideal.quotientMap J (algebraMap A B) hpJ).toAlgebra
  have hft : Algebra.FiniteType (A ⧸ p.asIdeal) (B ⧸ J) := by
    refine RingHom.FiniteType.of_comp_finiteType (f := Ideal.Quotient.mk p.asIdeal) ?_
    rw [Ideal.quotientMap_comp_mk]
    exact RingHom.FiniteType.comp_surjective (RingHom.finiteType_algebraMap.mpr inferInstance)
      Ideal.Quotient.mk_surjective
  have hJs : J ≤ p.asIdeal.comap (s : B →+* A) := by
    refine sup_le (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_) ?_
    · simpa using hx
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hc
  let s' : B ⧸ J →ₐ[A ⧸ p.asIdeal] A ⧸ p.asIdeal :=
    { Ideal.quotientMap p.asIdeal (s : B →+* A) hJs with
      commutes' := fun r ↦ by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        simp [RingHom.algebraMap_toAlgebra, Ideal.quotientMap_mk] }
  set φ' := comap (algebraMap (A ⧸ p.asIdeal) (B ⧸ J))
  set ψ := comap (Ideal.Quotient.mk J)
  set π := comap (Ideal.Quotient.mk p.asIdeal)
  have hcomm (q : PrimeSpectrum (B ⧸ J)) : comap (algebraMap A B) (ψ q) = π (φ' q) := by
    ext x
    simp [ψ, π, φ', RingHom.algebraMap_toAlgebra, Ideal.quotientMap_mk]
  have hrange : Set.range π = zeroLocus p.asIdeal := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  have himage (t : PrimeSpectrum (A ⧸ p.asIdeal)) :
      ψ '' (φ' ⁻¹' {t}) = comap (algebraMap A B) ⁻¹' {π t} ∩ zeroLocus {c} := by
    ext q
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨by simp [hcomm, Set.mem_singleton_iff.mp hq], ?_⟩
      simp only [ψ, mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe, comap_asIdeal,
        Ideal.mem_comap]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self c) : c ∈ J)]
      exact zero_mem _
    · rintro ⟨hq, hcq⟩
      have hJq : q ∈ Set.range ψ := by
        rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
          mem_zeroLocus, SetLike.coe_subset_coe]
        refine sup_le (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_) ?_
        · rw [Set.mem_preimage, Set.mem_singleton_iff] at hq
          have : π t ∈ zeroLocus p.asIdeal := hrange ▸ Set.mem_range_self t
          rw [← hq] at this
          exact this hx
        · simpa [Ideal.span_le] using hcq
      obtain ⟨q', rfl⟩ := hJq
      refine ⟨q', comap_injective_of_surjective _ Ideal.Quotient.mk_surjective ?_, rfl⟩
      exact (hcomm q').symm.trans hq
  have hψ : IsInducing ψ :=
    (isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).isInducing
  let t₀ : PrimeSpectrum (A ⧸ p.asIdeal) := ⟨⊥, Ideal.isPrime_bot⟩
  have hπ₀ : π t₀ = p := by
    ext x
    simp [π, t₀, Ideal.Quotient.eq_zero_iff_mem]
  have hgen : ConnectedSpace (PrimeSpectrum
      ((⊥ : Ideal (A ⧸ p.asIdeal)).ResidueField ⊗[A ⧸ p.asIdeal] (B ⧸ J))) := by
    refine (preimageHomeomorphFiber (A ⧸ p.asIdeal) (B ⧸ J) t₀).connectedSpace_iff.mp ?_
    rw [← isConnected_iff_connectedSpace]
    refine ⟨?_, ?_⟩
    · obtain ⟨q, hq⟩ := hconn.nonempty
      rw [← hπ₀, ← himage] at hq
      obtain ⟨q', hq', -⟩ := hq
      exact ⟨q', hq'⟩
    · rw [← hψ.isPreconnected_image, himage, hπ₀]
      exact hconn.isPreconnected
  obtain ⟨a', ha', H⟩ := exists_ne_zero_forall_connectedSpace_fiber _ s' hgen
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
  refine ⟨a, fun h ↦ ha' (Ideal.Quotient.eq_zero_iff_mem.mpr h), fun t hpt hat ↦ ?_⟩
  obtain ⟨t', rfl⟩ : t ∈ Set.range π := by
    rw [hrange]
    exact hpt
  rw [← himage]
  have := (preimageHomeomorphFiber _ _ t').connectedSpace_iff.mpr (H t' hat)
  exact (isConnected_iff_connectedSpace.mpr this).isPreconnected.image _ hψ.continuous.continuousOn


/-- The **relative connected component** of a section `s : B →ₐ[A] A`: the primes `q` of `B`
lying in the connected component of `s⁻¹ (q ∩ A)` in the fibre of `Spec B → Spec A` through `q`.
-/
def relativeComponent (s : B →ₐ[A] A) : Set (PrimeSpectrum B) :=
  {q | q ∈ connectedComponentIn (comap (algebraMap A B) ⁻¹' {comap (algebraMap A B) q})
    (comap (s : B →+* A) (comap (algebraMap A B) q))}

/-- **Generic structure of the relative component** (Stacks `055N`). Over a noetherian base, for
every prime `p` of `A` there are `a ∉ p` and `c ∈ B` such that over `V(p) ∩ D(a)` the relative
component is cut out by `c`. -/
theorem exists_forall_mem_relativeComponent_iff [IsNoetherianRing A] [Algebra.FiniteType A B]
    (s : B →ₐ[A] A) (p : PrimeSpectrum A) :
    ∃ a ∉ p.asIdeal, ∃ c : B, ∀ q : PrimeSpectrum B,
      comap (algebraMap A B) q ∈ zeroLocus p.asIdeal ∩ basicOpen a →
      (q ∈ relativeComponent s ↔ c ∈ q.asIdeal) := by
  obtain ⟨a₁, ha₁, b, c, H₁, hsc, hconn⟩ := exists_isConnected_preimage_inter_zeroLocus s p
  obtain ⟨a₂, ha₂, H₂⟩ := exists_forall_isPreconnected_preimage_inter_zeroLocus s p c hsc hconn
  refine ⟨a₁ * a₂, fun h ↦ (p.isPrime.mem_or_mem h).elim ha₁ ha₂, c, fun q ⟨hpq, haq⟩ ↦ ?_⟩
  set t := comap (algebraMap A B) q
  have hpt : p ≤ t := hpq
  have hat : a₁ * a₂ ∉ t.asIdeal := haq
  have hUV : comap (algebraMap A B) ⁻¹' {t} ∩ basicOpen b =
      comap (algebraMap A B) ⁻¹' {t} ∩ zeroLocus {c} := by
    ext q'
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
      mem_basicOpen, mem_zeroLocus, Set.singleton_subset_iff, and_congr_right_iff]
    intro hq'
    obtain ⟨hbc, hb⟩ := H₁ q' (hq' ▸ hpt) (hq' ▸ fun h ↦ hat (Ideal.mul_mem_right _ _ h))
    refine ⟨fun hb' ↦ (q'.isPrime.mem_or_mem hbc).resolve_left hb', fun hc hb' ↦ hb ?_⟩
    exact sub_mem hb' hc
  have hσ : comap (s : B →+* A) t ∈ comap (algebraMap A B) ⁻¹' {t} ∩ zeroLocus {c} := by
    refine ⟨?_, ?_⟩
    · ext x
      simp
    · simpa using hpt hsc
  rw [relativeComponent, Set.mem_ofPred_eq, connectedComponentIn_eq_of_inter_eq
    (isOpen_basicOpen (a := b)) (isClosed_zeroLocus {c}) hUV
    (H₂ t hpt fun h ↦ hat (Ideal.mul_mem_left _ _ h)) hσ]
  simp [t]

/-- **The relative connected component of a section is constructible** over a noetherian base
(Stacks `055N`, the noetherian case of `055P`). Let `A` be noetherian and `B` a finite type
`A`-algebra with a section `s`. The set of primes `q` of `B` lying in the connected component of
`s⁻¹ (q ∩ A)` in their fibre is constructible. -/
theorem isConstructible_relativeComponent [IsNoetherianRing A] [Algebra.FiniteType A B]
    (s : B →ₐ[A] A) : IsConstructible (relativeComponent s) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hopen {U : Set (PrimeSpectrum B)} (hU : IsOpen U) : IsConstructible U :=
    (TopologicalSpace.NoetherianSpace.isCompact U).isConstructible hU
  refine isConstructible_of_forall_exists_basicOpen (comap (algebraMap A B)) _ fun p ↦ ?_
  obtain ⟨a, ha, c, H⟩ := exists_forall_mem_relativeComponent_iff s p
  refine ⟨a, ha, ?_⟩
  have heq : relativeComponent s ∩ comap (algebraMap A B) ⁻¹' (zeroLocus p.asIdeal ∩ basicOpen a) =
      comap (algebraMap A B) ⁻¹' (zeroLocus p.asIdeal ∩ basicOpen a) ∩ zeroLocus {c} := by
    ext q
    refine ⟨fun ⟨hq, hq'⟩ ↦ ⟨hq', ?_⟩, fun ⟨hq', hq⟩ ↦ ⟨(H q hq').mpr ?_, hq'⟩⟩
    · simpa using (H q hq').mp hq
    · simpa using hq
  rw [heq, Set.preimage_inter]
  refine ((isConstructible_compl.mp (hopen ?_)).inter (hopen ?_)).inter
    (isConstructible_compl.mp (hopen ?_))
  · exact ((isClosed_zeroLocus _).preimage (continuous_comap (algebraMap A B))).isOpen_compl
  · exact (isOpen_basicOpen).preimage (continuous_comap (algebraMap A B))
  · exact (isClosed_zeroLocus _).isOpen_compl

end PrimeSpectrum
