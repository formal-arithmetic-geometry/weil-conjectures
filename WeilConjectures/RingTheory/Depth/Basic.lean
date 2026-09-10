/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Depth.Rees
public import Mathlib.RingTheory.KrullDimension.Regular
public import WeilConjectures.Mathlib.RingTheory.Regular.RegularSequence

/-!
# The depth of a module along an ideal

Let `R` be a commutative ring, `I : Ideal R` and `M` an `R`-module. We define the depth
`Module.depth I M : ℕ∞` of `M` along `I` as the supremum of the lengths of the `M`-regular
sequences with all entries in `I`.

## Design

Several definitions of depth are in use, and they agree for a nonzero finite module `M` over a
Noetherian local ring `R` and an ideal `I ≤ maximalIdeal R`:

* the supremum of the lengths of the `M`-regular sequences contained in `I` (the definition used
  here, `Module.depth`);
* the common length of the *maximal* `M`-regular sequences in `I`;
* the smallest `i` with `Ext^i(R/I, M) ≠ 0`.

The last equivalence is Rees' theorem, available in mathlib as
`ModuleCat.exists_isRegular_tfae`; it is what makes the definition chosen here usable, and it is
the engine behind `Module.depth_quotSMulTop_add_one` below.

Note that with this definition `depth I M = 0` when `M` is the zero module (there are no regular
sequences at all on the zero module, not even the empty one), rather than the value `⊤` that the
"maximal regular sequence" convention would give. All the results below therefore assume
`Nontrivial M`.

## Main definitions and results

* `Module.depth`: the depth of `M` along `I`.
* `Module.depth_eq_zero_iff`: the depth vanishes iff every element of `I` is a zerodivisor on `M`.
* `Module.depth_eq_zero_iff_exists_associatedPrime`: the depth vanishes iff `I` is contained in an
  associated prime of `M`.
* `Module.depth_quotSMulTop_add_one`: dividing by a regular element in `I` drops the depth by one.
* `Module.depth_le_supportDim`: the depth is at most the dimension of the support; in particular
  `Module.depth_le_ringKrullDim` for the ring itself.

-/

@[expose] public section

universe u v

open CategoryTheory Abelian Ideal IsLocalRing Pointwise RingTheory.Sequence

namespace Module

variable {R : Type u} [CommRing R] (I J : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The depth of a module `M` along an ideal `I`: the supremum of the lengths of the `M`-regular
sequences with all entries in `I`. See the module docstring for the design decisions behind this
definition; it is the intended notion only for a nonzero finite module over a Noetherian local
ring and an ideal contained in the maximal ideal. -/
noncomputable def depth : ℕ∞ :=
  ⨆ rs : {rs : List R // (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs}, (rs.1.length : ℕ∞)

variable {I J M}

lemma le_depth_of_isRegular {rs : List R} (mem : ∀ r ∈ rs, r ∈ I) (h : IsRegular M rs) :
    (rs.length : ℕ∞) ≤ depth I M :=
  le_iSup (fun rs : {rs : List R // (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs} ↦ (rs.1.length : ℕ∞))
    ⟨rs, mem, h⟩

lemma depth_le_iff {n : ℕ∞} :
    depth I M ≤ n ↔ ∀ rs : List R, (∀ r ∈ rs, r ∈ I) → IsRegular M rs → (rs.length : ℕ∞) ≤ n := by
  simp only [depth, iSup_le_iff, Subtype.forall, and_imp]

/-- The depth is monotone in the ideal. -/
lemma depth_mono (h : I ≤ J) : depth I M ≤ depth J M :=
  depth_le_iff.mpr fun _ mem reg ↦ le_depth_of_isRegular (fun r hr ↦ h (mem r hr)) reg

variable (I M) in
@[simp]
lemma depth_eq_zero_of_subsingleton [Subsingleton M] : depth I M = 0 := by
  have : IsEmpty {rs : List R // (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs} :=
    ⟨fun rs ↦ rs.2.2.top_ne_smul (Subsingleton.elim _ _)⟩
  simp [depth]

section Local

variable [IsLocalRing R] [Nontrivial M] [Module.Finite R M] (hI : I ≤ maximalIdeal R)
include hI

/-- The depth of `M` along `I` vanishes exactly when every element of `I` is a zerodivisor
on `M`. -/
lemma depth_eq_zero_iff : depth I M = 0 ↔ ∀ r ∈ I, ¬ IsSMulRegular M r := by
  rw [← le_zero_iff, depth_le_iff]
  refine ⟨fun h r hr hreg ↦ ?_, fun h rs mem reg ↦ ?_⟩
  · simpa using h [r] (by simpa using hr)
      ((IsLocalRing.isRegular_singleton_iff (hI hr)).mpr hreg)
  · match rs with
    | [] => simp
    | a :: rs' =>
      exact absurd ((isRegular_cons_iff M a rs').mp reg).1 (h a (mem a List.mem_cons_self))

/-- The depth of `M` along `I` vanishes exactly when there is a nonzero map `R ⧸ I → M`. -/
lemma depth_eq_zero_iff_nontrivial_linearMap [IsNoetherianRing R] :
    depth I M = 0 ↔ Nontrivial ((R ⧸ I) →ₗ[R] M) := by
  rw [depth_eq_zero_iff hI, ← not_subsingleton_iff_nontrivial,
    IsSMulRegular.subsingleton_linearMap_iff, Ideal.annihilator_quotient]
  exact ⟨fun h ⟨r, hr, hreg⟩ ↦ h r hr hreg, fun h r hr hreg ↦ h ⟨r, hr, hreg⟩⟩

/-- The depth of `M` along `I` vanishes exactly when `I` is contained in an associated prime
of `M`. -/
lemma depth_eq_zero_iff_exists_associatedPrime [IsNoetherianRing R] :
    depth I M = 0 ↔ ∃ p ∈ associatedPrimes R M, I ≤ p := by
  rw [depth_eq_zero_iff hI]
  refine ⟨fun h ↦ ?_, fun ⟨p, hp, hle⟩ r hr hreg ↦ ?_⟩
  · obtain ⟨q, hq⟩ := associatedPrimes.nonempty R M
    refine (Ideal.subset_union_prime_finite (associatedPrimes.finite R M) q q
      (fun p hp _ _ ↦ hp.isPrime)).mp ?_
    rw [biUnion_associatedPrimes_eq_compl_regular R M]
    exact fun r hr ↦ h r hr
  · refine absurd hreg ?_
    have : r ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) :=
      Set.mem_biUnion hp (hle hr)
    rw [biUnion_associatedPrimes_eq_compl_regular R M] at this
    exact this

end Local

section Rees

variable [Small.{v} R] [IsNoetherianRing R] [Module.Finite R M]

variable (I) in
/-- The `R`-module `R ⧸ I`, viewed as an object of `ModuleCat.{v} R`. -/
private noncomputable abbrev quotObj : ModuleCat.{v} R := ModuleCat.of R (Shrink.{v} (R ⧸ I))

omit [IsNoetherianRing R] in
private lemma support_quotObj :
    Module.support R (quotObj.{u, v} I) = PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [(Shrink.linearEquiv R (R ⧸ I)).support_eq, Module.support_eq_zeroLocus,
    Ideal.annihilator_quotient]

/-- If `M` has a regular sequence of length `n + 1` in `I` and `x ∈ I` is `M`-regular, then
`M ⧸ xM` has a regular sequence of length `n` in `I`. This is the nontrivial half of
`Module.depth_quotSMulTop_add_one`; it rests on Rees' theorem via the vanishing of
`Ext^i(R ⧸ I, -)`. -/
lemma exists_isRegular_quotSMulTop_of_isRegular
    (hlt : I • (⊤ : Submodule R M) < ⊤) {x : R} (hx : IsSMulRegular M x)
    (hlt' : I • (⊤ : Submodule R (QuotSMulTop x M)) < ⊤)
    {rs : List R} (mem : ∀ r ∈ rs, r ∈ I) (reg : IsRegular M rs) {n : ℕ} (hn : n < rs.length) :
    ∃ ss : List R, ss.length = n ∧ (∀ r ∈ ss, r ∈ I) ∧ IsRegular (QuotSMulTop x M) ss := by
  have hsupp := support_quotObj.{u, v} (I := I)
  have hext : ∀ i < rs.length, Subsingleton (Ext (quotObj.{u, v} I) (ModuleCat.of R M) i) :=
    ModuleCat.subsingleton_ext_of_exists_isRegular I _ hsupp.subset (ModuleCat.of R M) hlt rs
      mem reg
  have hext' : ∀ i < n,
      Subsingleton (Ext (quotObj.{u, v} I) (ModuleCat.of R (QuotSMulTop x M)) i) := by
    intro i hi
    have zero1 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hext i (by omega))
    have zero2 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hext (i + 1) (by omega))
    have hse : (ModuleCat.smulShortComplex (ModuleCat.of R M) x).ShortExact :=
      IsSMulRegular.smulShortComplex_shortExact hx
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      (Ext.covariant_sequence_exact₃' (quotObj.{u, v} I) hse i (i + 1) rfl)
      (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
  exact ModuleCat.exists_isRegular_of_exists_subsingleton_ext I n
    (ModuleCat.of R (QuotSMulTop x M)) hlt' _ hsupp hext'

end Rees

section Main

variable [IsNoetherianRing R] [IsLocalRing R] [Nontrivial M] [Module.Finite R M]

/-- The depth of `M` along `I` is at most the dimension of the support of `M`. -/
theorem depth_le_supportDim : (depth I M : WithBot ℕ∞) ≤ supportDim R M := by
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (supportDim_ne_bot_of_nontrivial R M)
  rw [← hd, WithBot.coe_le_coe, depth_le_iff]
  intro rs mem reg
  have key := supportDim_add_length_eq_supportDim_of_isRegular rs reg
  have := reg.quot_ofList_smul_nontrivial ⊤
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp
    (supportDim_ne_bot_of_nontrivial R (M ⧸ ofList rs • (⊤ : Submodule R M)))
  rw [← he, ← hd] at key
  have : e + (rs.length : ℕ∞) = d := by exact_mod_cast key
  exact this ▸ le_add_self

/-- The depth of a finite nonzero module over a Noetherian local ring is finite. -/
theorem depth_ne_top : depth I M ≠ ⊤ := by
  intro h
  have hle := depth_le_supportDim (I := I) (M := M)
  rw [h] at hle
  exact absurd (le_antisymm le_top
    (le_trans (by simpa using hle) (supportDim_le_ringKrullDim R M))) ringKrullDim_lt_top.ne

variable (hI : I ≤ maximalIdeal R)
include hI

/-- Dividing out by a regular element of `I` drops the depth along `I` by exactly one. -/
theorem depth_quotSMulTop_add_one [Small.{v} R] {x : R} (hx : x ∈ I) (hreg : IsSMulRegular M x) :
    depth I (QuotSMulTop x M) + 1 = depth I M := by
  have hxm : x ∈ maximalIdeal R := hI hx
  have hne : Nontrivial (QuotSMulTop x M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M hxm
  refine le_antisymm ?_ ?_
  · have : Nonempty {rs : List R // (∀ r ∈ rs, r ∈ I) ∧ IsRegular (QuotSMulTop x M) rs} :=
      ⟨⟨[], by simp, IsRegular.nil R (QuotSMulTop x M)⟩⟩
    rw [depth, ENat.iSup_add]
    refine iSup_le fun ss ↦ ?_
    have hcons : IsRegular M (x :: ss.1) := (isRegular_cons_iff M x ss.1).mpr ⟨hreg, ss.2.2⟩
    have := le_depth_of_isRegular (rs := x :: ss.1)
      (fun r hr ↦ by rcases List.mem_cons.mp hr with rfl | hr; exacts [hx, ss.2.1 r hr]) hcons
    simpa [add_comm] using this
  · rw [depth_le_iff]
    intro rs mem reg
    match rs with
    | [] => simp
    | a :: rs' =>
      obtain ⟨ss, len, memss, regss⟩ := exists_isRegular_quotSMulTop_of_isRegular
        (Submodule.ideal_smul_top_lt_top hI) hreg (Submodule.ideal_smul_top_lt_top hI) mem reg
        (n := rs'.length) (by simp)
      have := le_depth_of_isRegular memss regss
      rw [len] at this
      simpa [add_comm] using add_le_add_right this 1

end Main

section Self

variable [IsNoetherianRing R] [IsLocalRing R]

/-- The depth of a Noetherian local ring along an ideal is at most its Krull dimension. -/
theorem depth_le_ringKrullDim : (depth I R : WithBot ℕ∞) ≤ ringKrullDim R := by
  rw [← supportDim_self_eq_ringKrullDim]
  exact depth_le_supportDim

end Self

end Module
