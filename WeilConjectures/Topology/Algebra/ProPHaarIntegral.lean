/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# The `ℓ`-adic Haar integral on a pro-`p` group

Let `G` be a compact totally disconnected topological group in which every open normal subgroup
has index a power of a prime `p`, and let `ℓ ≠ p` be another prime. We construct the normalized
Haar integral `ProPGroup.haarIntegral : C(G, ℤ_[ℓ]) →ₗ[ℤ_[ℓ]] ℤ_[ℓ]`.

For a subgroup `U` of finite index, `Subgroup.cosetAverage U f` is the normalized average
`[G : U]⁻¹ ∑_{gU ∈ G / U} f g` over coset representatives; it makes sense in `ℤ_[ℓ]` as soon as
`[G : U]` is a unit of `ℤ_[ℓ]`. If `f (x * u) = f x` for `u ∈ U`, then the average over any
`V ≤ U` agrees with the average over `U`. A continuous `f` is uniformly approximated by such
functions, so the net of averages over the open normal subgroups (directed downwards) is Cauchy,
and the Haar integral is its limit.

## Main results

* `ProPGroup.haarIntegral_one`: the integral is normalized.
* `ProPGroup.haarIntegral_comp_mulLeft`: the integral is left invariant.
* `ProPGroup.haarIntegral_eq_inverse_index_mul_sum`: for `f` constant on the cosets of an
  open normal subgroup `U`, the integral is `[G : U]⁻¹ ∑_{gU ∈ G / U} f g`.
-/

@[expose] public section

open Filter Topology

variable {G : Type*} [Group G]

namespace Subgroup

/-- If `F` is invariant under right multiplication by `U` and `V ≤ U`, then `F` takes the same
value at `x` and at the chosen representative of the coset `x V`. -/
theorem apply_out_mk_of_le {M : Type*} {U V : Subgroup G} (hle : V ≤ U) {F : G → M}
    (hF : ∀ x, ∀ u ∈ U, F (x * u) = F x) (x : G) : F (QuotientGroup.mk x : G ⧸ V).out = F x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul V x
  rw [hh, hF x h (hle h.2)]

/-- Refining the cosets: if `F` is invariant under right multiplication by `U` and `V ≤ U`, then
`[G : U] • ∑_{G / V} F = [G : V] • ∑_{G / U} F`, summing over coset representatives. -/
theorem index_smul_finsum_out_eq {M : Type*} [AddCommMonoid M] {U V : Subgroup G} (hle : V ≤ U)
    [Finite (G ⧸ U)] [Finite (G ⧸ V)] {F : G → M} (hF : ∀ x, ∀ u ∈ U, F (x * u) = F x) :
    U.index • ∑ᶠ q : G ⧸ V, F q.out = V.index • ∑ᶠ q : G ⧸ U, F q.out := by
  classical
  let e := Subgroup.quotientEquivProdOfLE hle
  have : Finite ((G ⧸ U) × (U ⧸ V.subgroupOf U)) := Finite.of_equiv _ e
  have : Finite (U ⧸ V.subgroupOf U) := Finite.prod_right (G ⧸ U)
  have := Fintype.ofFinite (G ⧸ U)
  have := Fintype.ofFinite (G ⧸ V)
  have := Fintype.ofFinite (U ⧸ V.subgroupOf U)
  have hV : V.index = U.index * Nat.card (U ⧸ V.subgroupOf U) := by
    rw [index_eq_card, index_eq_card, Nat.card_congr e, Nat.card_prod]
  have hsum : ∑ᶠ q : G ⧸ V, F q.out =
      Nat.card (U ⧸ V.subgroupOf U) • ∑ᶠ q : G ⧸ U, F q.out := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← e.symm.sum_comp,
      Fintype.sum_prod_type, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun b _ => ?_
    induction b using QuotientGroup.induction_on with
    | H b =>
      rw [quotientEquivProdOfLE_symm_apply]
      exact (apply_out_mk_of_le hle hF _).trans (hF _ _ b.2)
  rw [hsum, hV, smul_smul]

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- The normalized coset average `[G : U]⁻¹ ∑_{gU ∈ G / U} f g` of a function `f : G → ℤ_[ℓ]`,
using the chosen coset representatives. It is meaningful when `[G : U]` is a unit of `ℤ_[ℓ]`. -/
noncomputable def cosetAverage (U : Subgroup G) (f : G → ℤ_[ℓ]) : ℤ_[ℓ] :=
  Ring.inverse (U.index : ℤ_[ℓ]) * ∑ᶠ q : G ⧸ U, f q.out

/-- Multiplying the coset average by the index recovers the sum over coset representatives. -/
theorem index_mul_cosetAverage {U : Subgroup G} (hU : IsUnit (U.index : ℤ_[ℓ]))
    (f : G → ℤ_[ℓ]) : (U.index : ℤ_[ℓ]) * U.cosetAverage f = ∑ᶠ q : G ⧸ U, f q.out := by
  rw [cosetAverage, ← mul_assoc, Ring.mul_inverse_cancel _ hU, one_mul]

/-- The coset average of a constant function is its value. -/
theorem cosetAverage_const {U : Subgroup G} [Finite (G ⧸ U)] (hU : IsUnit (U.index : ℤ_[ℓ]))
    (c : ℤ_[ℓ]) : U.cosetAverage (fun _ => c) = c := by
  have := Fintype.ofFinite (G ⧸ U)
  rw [cosetAverage, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, ← index_eq_card, nsmul_eq_mul, ← mul_assoc,
    Ring.inverse_mul_cancel _ hU, one_mul]

/-- The coset average is additive. -/
theorem cosetAverage_add (U : Subgroup G) [Finite (G ⧸ U)] (f g : G → ℤ_[ℓ]) :
    U.cosetAverage (f + g) = U.cosetAverage f + U.cosetAverage g := by
  have := Fintype.ofFinite (G ⧸ U)
  simp [cosetAverage, finsum_eq_sum_of_fintype, Finset.sum_add_distrib, mul_add]

/-- The coset average commutes with subtraction. -/
theorem cosetAverage_sub (U : Subgroup G) [Finite (G ⧸ U)] (f g : G → ℤ_[ℓ]) :
    U.cosetAverage (f - g) = U.cosetAverage f - U.cosetAverage g := by
  have := Fintype.ofFinite (G ⧸ U)
  simp [cosetAverage, finsum_eq_sum_of_fintype, Finset.sum_sub_distrib, mul_sub]

/-- The coset average is `ℤ_[ℓ]`-homogeneous. -/
theorem cosetAverage_smul (U : Subgroup G) [Finite (G ⧸ U)] (c : ℤ_[ℓ]) (f : G → ℤ_[ℓ]) :
    U.cosetAverage (c • f) = c * U.cosetAverage f := by
  have := Fintype.ofFinite (G ⧸ U)
  simp [cosetAverage, finsum_eq_sum_of_fintype, ← Finset.mul_sum, mul_left_comm]

/-- The coset average of a function invariant under right multiplication by `U` does not change
when `U` is replaced by a smaller subgroup `V` (both of index invertible in `ℤ_[ℓ]`). -/
theorem cosetAverage_eq_of_le {U V : Subgroup G} (hle : V ≤ U) [Finite (G ⧸ U)]
    [Finite (G ⧸ V)] (hU : IsUnit (U.index : ℤ_[ℓ])) (hV : IsUnit (V.index : ℤ_[ℓ]))
    {f : G → ℤ_[ℓ]} (hf : ∀ x, ∀ u ∈ U, f (x * u) = f x) :
    V.cosetAverage f = U.cosetAverage f := by
  refine (hU.mul hV).mul_left_cancel ?_
  have h := index_smul_finsum_out_eq hle hf
  rw [nsmul_eq_mul, nsmul_eq_mul, ← index_mul_cosetAverage hU, ← index_mul_cosetAverage hV] at h
  linear_combination h

/-- The norm of a coset average is bounded by a uniform bound on the function. -/
theorem norm_cosetAverage_le {U : Subgroup G} [Finite (G ⧸ U)] (hU : IsUnit (U.index : ℤ_[ℓ]))
    {f : G → ℤ_[ℓ]} {ε : ℝ} (hε : 0 ≤ ε) (hf : ∀ x, ‖f x‖ ≤ ε) : ‖U.cosetAverage f‖ ≤ ε := by
  have := Fintype.ofFinite (G ⧸ U)
  rw [cosetAverage, norm_mul, PadicInt.isUnit_iff.mp hU.ringInverse, one_mul,
    finsum_eq_sum_of_fintype]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε fun q _ => hf _

/-- If `f` varies by at most `ε` on right `U`-cosets, then it is `ε`-close to the function
`x ↦ f (xU).out`. -/
theorem norm_sub_apply_out_mk_le {U : Subgroup G} {f : G → ℤ_[ℓ]} {ε : ℝ}
    (hf : ∀ x, ∀ u ∈ U, ‖f (x * u) - f x‖ ≤ ε) (y : G) :
    ‖f y - f (QuotientGroup.mk y : G ⧸ U).out‖ ≤ ε := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U y
  rw [hh, norm_sub_rev]
  exact hf y h h.2

/-- If `f` varies by at most `ε` on right `U`-cosets, then the coset averages of `f` over `U`
and over any `V ≤ U` differ by at most `ε`. -/
theorem norm_cosetAverage_sub_le_of_le {U V : Subgroup G} (hle : V ≤ U) [Finite (G ⧸ U)]
    [Finite (G ⧸ V)] (hU : IsUnit (U.index : ℤ_[ℓ])) (hV : IsUnit (V.index : ℤ_[ℓ]))
    {f : G → ℤ_[ℓ]} {ε : ℝ} (hε : 0 ≤ ε) (hf : ∀ x, ∀ u ∈ U, ‖f (x * u) - f x‖ ≤ ε) :
    ‖V.cosetAverage f - U.cosetAverage f‖ ≤ ε := by
  set F : G → ℤ_[ℓ] := fun x => f (QuotientGroup.mk x : G ⧸ U).out
  have hFU : U.cosetAverage F = U.cosetAverage f := by
    simp [cosetAverage, F]
  have hF (x : G) (u : G) (hu : u ∈ U) : F (x * u) = F x := by
    simp [F, QuotientGroup.mk_mul_of_mem x hu]
  rw [← hFU, ← cosetAverage_eq_of_le hle hU hV hF, ← cosetAverage_sub]
  exact norm_cosetAverage_le hV hε fun x => norm_sub_apply_out_mk_le hf x

/-- If `f` varies by at most `ε` on right `U`-cosets, then left translating `f` changes its
coset average over `U` by at most `ε`. -/
theorem norm_cosetAverage_comp_mul_left_sub_le {U : Subgroup G} [Finite (G ⧸ U)]
    (hU : IsUnit (U.index : ℤ_[ℓ])) {f : G → ℤ_[ℓ]} {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ x, ∀ u ∈ U, ‖f (x * u) - f x‖ ≤ ε) (g : G) :
    ‖U.cosetAverage (fun x => f (g * x)) - U.cosetAverage f‖ ≤ ε := by
  set F : G → ℤ_[ℓ] := fun x => f (QuotientGroup.mk x : G ⧸ U).out
  have hFU : U.cosetAverage F = U.cosetAverage f := by
    simp [cosetAverage, F]
  have hshift : U.cosetAverage (fun x => F (g * x)) = U.cosetAverage F := by
    rw [cosetAverage, cosetAverage]
    conv_rhs => rw [← finsum_comp_equiv (MulAction.toPerm g : G ⧸ U ≃ G ⧸ U)]
    congr 2
    funext q
    have hq : g • q = (QuotientGroup.mk (g * q.out) : G ⧸ U) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    simp only [MulAction.toPerm_apply, hq, F, QuotientGroup.out_eq']
  rw [← hFU, ← hshift, ← cosetAverage_sub]
  exact norm_cosetAverage_le hU hε fun x => norm_sub_apply_out_mk_le hf (g * x)

end Subgroup

section Topological

variable [TopologicalSpace G]

/-- The whole group is an open normal subgroup. -/
instance OpenNormalSubgroup.instNonempty : Nonempty (OpenNormalSubgroup G) :=
  ⟨{ toOpenSubgroup := ⊤
     isNormal' := by
       rw [OpenSubgroup.toSubgroup_top]
       infer_instance }⟩

namespace ProPGroup

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- In a group whose open normal subgroups have `p`-power index, these indices are units in
`ℤ_[ℓ]` for every prime `ℓ ≠ p`. -/
theorem isUnit_index {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hG : ∀ U : OpenNormalSubgroup G, ∃ k, U.toSubgroup.index = p ^ k)
    (U : OpenNormalSubgroup G) : IsUnit ((U : Subgroup G).index : ℤ_[ℓ]) := by
  obtain ⟨k, hk⟩ := hG U
  rw [hk, PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact Nat.Coprime.pow_right k ((Nat.coprime_primes Fact.out hp).2 hpℓ.symm)

end ProPGroup

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- A continuous function on a compact totally disconnected group into a normed group is
uniformly approximated by functions constant on the cosets of an open normal subgroup: it varies
by at most `ε` on every coset `x U`. -/
theorem ContinuousMap.exists_openNormalSubgroup_norm_sub_le {E : Type*}
    [SeminormedAddCommGroup E] (f : C(G, E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : OpenNormalSubgroup G, ∀ x, ∀ u ∈ U, ‖f (x * u) - f x‖ ≤ ε := by
  let n : Set (G × G) := {p | ‖f (p.1 * p.2) - f p.1‖ < ε}
  have hn : IsOpen n := isOpen_lt
    ((f.continuous.comp continuous_mul).sub (f.continuous.comp continuous_fst)).norm
    continuous_const
  have hsub : (Set.univ : Set G) ×ˢ {1} ⊆ n := by
    rintro ⟨x, y⟩ ⟨-, hy⟩
    obtain rfl : y = 1 := hy
    simp [n, hε]
  obtain ⟨u, v, -, hv, hu, h1v, huv⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hn hsub
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hv (h1v rfl)
  refine ⟨U, fun x w hw => ?_⟩
  have hxw : (x, w) ∈ n := huv (Set.mk_mem_prod (hu (Set.mem_univ x)) (hU hw))
  exact le_of_lt hxw

namespace ProPGroup

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- The net of coset averages of a continuous function over the open normal subgroups, directed
downwards, is Cauchy. -/
theorem cauchy_map_cosetAverage
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ]))
    (f : C(G, ℤ_[ℓ])) :
    Cauchy (map (fun U : OpenNormalSubgroup G => (U : Subgroup G).cosetAverage f) atBot) := by
  rw [Metric.cauchy_iff]
  refine ⟨map_neBot, fun ε hε => ?_⟩
  obtain ⟨U, hU⟩ := f.exists_openNormalSubgroup_norm_sub_le (by positivity : 0 < ε / 4)
  refine ⟨_, image_mem_map (Iic_mem_atBot U), ?_⟩
  rintro _ ⟨V, hV, rfl⟩ _ ⟨W, hW, rfl⟩
  have h1 := Subgroup.norm_cosetAverage_sub_le_of_le (fun x hx => hV hx) (hG U) (hG V)
    (by positivity) hU
  have h2 := Subgroup.norm_cosetAverage_sub_le_of_le (fun x hx => hW hx) (hG U) (hG W)
    (by positivity) hU
  rw [dist_eq_norm]
  calc _ = ‖((V : Subgroup G).cosetAverage f - (U : Subgroup G).cosetAverage f) -
        ((W : Subgroup G).cosetAverage f - (U : Subgroup G).cosetAverage f)‖ := by
          congr 1
          abel
    _ ≤ _ := norm_sub_le _ _
    _ < ε := by linarith

/-- The net of coset averages of a continuous function converges. -/
theorem exists_tendsto_cosetAverage
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ]))
    (f : C(G, ℤ_[ℓ])) : ∃ a : ℤ_[ℓ],
      Tendsto (fun U : OpenNormalSubgroup G => (U : Subgroup G).cosetAverage f) atBot (𝓝 a) :=
  CompleteSpace.complete (cauchy_map_cosetAverage hG f)

/-- The `ℓ`-adic Haar integral on a compact totally disconnected group all of whose open normal
subgroups have index invertible in `ℤ_[ℓ]`: the limit of the coset averages over the open normal
subgroups. -/
noncomputable def haarIntegralOfIsUnit
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ])) :
    C(G, ℤ_[ℓ]) →ₗ[ℤ_[ℓ]] ℤ_[ℓ] where
  toFun f := limUnder atBot fun U : OpenNormalSubgroup G => (U : Subgroup G).cosetAverage f
  map_add' f g := by
    refine tendsto_nhds_unique (tendsto_nhds_limUnder (exists_tendsto_cosetAverage hG (f + g))) ?_
    simp_rw [ContinuousMap.coe_add, Subgroup.cosetAverage_add]
    exact (tendsto_nhds_limUnder (exists_tendsto_cosetAverage hG f)).add
      (tendsto_nhds_limUnder (exists_tendsto_cosetAverage hG g))
  map_smul' c f := by
    refine tendsto_nhds_unique (tendsto_nhds_limUnder (exists_tendsto_cosetAverage hG (c • f))) ?_
    simp_rw [ContinuousMap.coe_smul, Subgroup.cosetAverage_smul]
    exact (tendsto_nhds_limUnder (exists_tendsto_cosetAverage hG f)).const_mul c

/-- The coset averages of `f` converge to the Haar integral of `f`. -/
theorem tendsto_cosetAverage_haarIntegralOfIsUnit
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ]))
    (f : C(G, ℤ_[ℓ])) :
    Tendsto (fun U : OpenNormalSubgroup G => (U : Subgroup G).cosetAverage f) atBot
      (𝓝 (haarIntegralOfIsUnit hG f)) :=
  tendsto_nhds_limUnder (exists_tendsto_cosetAverage hG f)

/-- For `f` invariant under right multiplication by an open normal subgroup `U`, the integral
is the coset average over `U`. -/
theorem haarIntegralOfIsUnit_eq_cosetAverage
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ]))
    (U : OpenNormalSubgroup G) {f : C(G, ℤ_[ℓ])} (hf : ∀ x, ∀ u ∈ U, f (x * u) = f x) :
    haarIntegralOfIsUnit hG f = (U : Subgroup G).cosetAverage f := by
  refine tendsto_nhds_unique (tendsto_cosetAverage_haarIntegralOfIsUnit hG f)
    (tendsto_const_nhds.congr' ?_)
  filter_upwards [Iic_mem_atBot U] with V hV
  exact (Subgroup.cosetAverage_eq_of_le (fun x hx => hV hx) (hG U) (hG V) hf).symm

/-- The Haar integral of a constant function is its value. -/
theorem haarIntegralOfIsUnit_const
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ])) (c : ℤ_[ℓ]) :
    haarIntegralOfIsUnit hG (ContinuousMap.const G c) = c := by
  let U : OpenNormalSubgroup G := Classical.arbitrary _
  rw [haarIntegralOfIsUnit_eq_cosetAverage hG U fun _ _ _ => rfl]
  exact Subgroup.cosetAverage_const (hG U) c

/-- Left invariance of the Haar integral. -/
theorem haarIntegralOfIsUnit_comp_mulLeft
    (hG : ∀ U : OpenNormalSubgroup G, IsUnit ((U : Subgroup G).index : ℤ_[ℓ]))
    (f : C(G, ℤ_[ℓ])) (g : G) :
    haarIntegralOfIsUnit hG (f.comp (ContinuousMap.mulLeft g)) = haarIntegralOfIsUnit hG f := by
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨U, hU⟩ := f.exists_openNormalSubgroup_norm_sub_le hε
  refine le_of_tendsto ((tendsto_cosetAverage_haarIntegralOfIsUnit hG _).dist
    (tendsto_cosetAverage_haarIntegralOfIsUnit hG f)) ?_
  filter_upwards [Iic_mem_atBot U] with V hV
  rw [dist_eq_norm]
  exact Subgroup.norm_cosetAverage_comp_mul_left_sub_le (hG V) hε.le
    (fun x u hu => hU x u (hV hu)) g

/-- The normalized left invariant `ℓ`-adic Haar integral on a compact totally disconnected group
`G` all of whose open normal subgroups have `p`-power index, for primes `p ≠ ℓ`. -/
noncomputable def haarIntegral {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hG : ∀ U : OpenNormalSubgroup G, ∃ k, U.toSubgroup.index = p ^ k) :
    C(G, ℤ_[ℓ]) →ₗ[ℤ_[ℓ]] ℤ_[ℓ] :=
  haarIntegralOfIsUnit (isUnit_index hp hpℓ hG)

/-- The Haar integral of a constant function is its value. -/
theorem haarIntegral_const {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hG : ∀ U : OpenNormalSubgroup G, ∃ k, U.toSubgroup.index = p ^ k) (c : ℤ_[ℓ]) :
    haarIntegral hp hpℓ hG (ContinuousMap.const G c) = c :=
  haarIntegralOfIsUnit_const _ c

/-- The Haar integral is normalized. -/
theorem haarIntegral_one {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hG : ∀ U : OpenNormalSubgroup G, ∃ k, U.toSubgroup.index = p ^ k) :
    haarIntegral hp hpℓ hG 1 = 1 :=
  haarIntegral_const hp hpℓ hG 1

/-- The Haar integral is left invariant. -/
theorem haarIntegral_comp_mulLeft {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hG : ∀ U : OpenNormalSubgroup G, ∃ k, U.toSubgroup.index = p ^ k) (f : C(G, ℤ_[ℓ]))
    (g : G) :
    haarIntegral hp hpℓ hG (f.comp (ContinuousMap.mulLeft g)) = haarIntegral hp hpℓ hG f :=
  haarIntegralOfIsUnit_comp_mulLeft _ f g

/-- For `f` constant on the cosets of an open normal subgroup `U`, the Haar integral of `f` is
the coset average of `f` over `U`. -/
theorem haarIntegral_eq_cosetAverage {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hG : ∀ U : OpenNormalSubgroup G, ∃ k, U.toSubgroup.index = p ^ k)
    (U : OpenNormalSubgroup G) {f : C(G, ℤ_[ℓ])} (hf : ∀ x, ∀ u ∈ U, f (x * u) = f x) :
    haarIntegral hp hpℓ hG f = U.toSubgroup.cosetAverage f :=
  haarIntegralOfIsUnit_eq_cosetAverage _ U hf

/-- For `f` constant on the cosets of an open normal subgroup `U`, the Haar integral of `f` is
`[G : U]⁻¹ ∑_{gU ∈ G / U} f g`. -/
theorem haarIntegral_eq_inverse_index_mul_sum {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hG : ∀ U : OpenNormalSubgroup G, ∃ k, U.toSubgroup.index = p ^ k)
    (U : OpenNormalSubgroup G) [Fintype (G ⧸ U.toSubgroup)] {f : C(G, ℤ_[ℓ])}
    (hf : ∀ x, ∀ u ∈ U, f (x * u) = f x) :
    haarIntegral hp hpℓ hG f =
      Ring.inverse (U.toSubgroup.index : ℤ_[ℓ]) * ∑ q : G ⧸ U.toSubgroup, f q.out := by
  rw [haarIntegral_eq_cosetAverage hp hpℓ hG U hf, Subgroup.cosetAverage,
    finsum_eq_sum_of_fintype]

/-- For `f` constant on the cosets of an open normal subgroup `U`, the Haar integral of `f`
times `[G : U]` is the sum of `f` over coset representatives. -/
theorem index_mul_haarIntegral {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hG : ∀ U : OpenNormalSubgroup G, ∃ k, U.toSubgroup.index = p ^ k)
    (U : OpenNormalSubgroup G) [Fintype (G ⧸ U.toSubgroup)] {f : C(G, ℤ_[ℓ])}
    (hf : ∀ x, ∀ u ∈ U, f (x * u) = f x) :
    (U.toSubgroup.index : ℤ_[ℓ]) * haarIntegral hp hpℓ hG f = ∑ q : G ⧸ U.toSubgroup, f q.out := by
  rw [haarIntegral_eq_cosetAverage hp hpℓ hG U hf,
    Subgroup.index_mul_cosetAverage (isUnit_index hp hpℓ hG U), finsum_eq_sum_of_fintype]

end ProPGroup

end Topological
