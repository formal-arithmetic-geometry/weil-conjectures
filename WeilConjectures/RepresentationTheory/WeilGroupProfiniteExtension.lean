/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RepresentationTheory.FiniteDimensionalRealization
public import WeilConjectures.RepresentationTheory.WeilGroupLattice
public import WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Bounded representations of a dense Weil group extend to the profinite group

Let `ι : W → Π` be a homomorphism with dense image from a group `W` with a degree
`deg : W → ℤ` into a profinite group `Π` (for instance the Weil group `π₁(X, t) ⋊ ℤ` of a scheme
`X₀` over a finite field inside its arithmetic fundamental group `π₁(X₀)`), such that the
geometric part `ker deg = κ(G)`, `G` compact, embeds into `Π`, and such that the degree is
continuous for the topology induced by `Π`. Then a finite-dimensional `ℚ̄_ℓ`-representation of `W`
which is continuous on `G` and bounded on `W` extends to a continuous representation of `Π`
(Deligne, Weil II, 1.3.14 and 1.1.7): it stabilises a lattice
(`MonoidHom.exists_lattice_of_isWeaklyBounded_of_compactSpace`), its reductions modulo `ℓᵏ`
factor through open subgroups of `Π`, and the closure of its graph is the
graph of a continuous extension.

## Main results

* `MonoidHom.exists_continuous_extend_of_forall_nhds_one`: a homomorphism `f : W → M` to a
  compact Hausdorff topological monoid which is continuous at `1` for the topology induced by
  a dense `ι : W → Π`, `Π` compact, extends to a continuous homomorphism `Π → M` (closed graph).
* `Representation.exists_extension_of_isBoundedOn`: the extension of bounded representations.
-/

@[expose] public section

open Topology

namespace MonoidHom

/-- **Extension of homomorphisms from a dense subgroup** (closed graph argument). Let
`ι : W →* Π` have dense range in a compact Hausdorff group `Π`, and let `f : W →* M` be a
homomorphism to a compact Hausdorff topological monoid which is continuous at `1` for the
topology induced by `ι`: for every neighbourhood `V` of `1` in `M` there is a neighbourhood `U` of
`1` in `Π` with `f w ∈ V` whenever `ι w ∈ U`. Then `f` extends to a continuous homomorphism
`F : Π →* M`, `F ∘ ι = f`. -/
theorem exists_continuous_extend_of_forall_nhds_one {W P M : Type*} [Group W] [Group P]
    [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [Monoid M]
    [TopologicalSpace M] [ContinuousMul M] [CompactSpace M] [T2Space M] (ι : W →* P)
    (hι : DenseRange ι) (f : W →* M)
    (hf : ∀ V ∈ 𝓝 (1 : M), ∃ U ∈ 𝓝 (1 : P), ∀ w, ι w ∈ U → f w ∈ V) :
    ∃ F : P →* M, Continuous F ∧ ∀ w, F (ι w) = f w := by
  set Γ : Submonoid (P × M) := (MonoidHom.mrange (ι.prod f)).topologicalClosure
  have hΓc : IsClosed (Γ : Set (P × M)) := Submonoid.isClosed_topologicalClosure _
  have hgr (w : W) : (ι w, f w) ∈ Γ := Submonoid.le_topologicalClosure _ ⟨w, rfl⟩
  -- the fibre of `Γ` over `1` is `{1}`
  have hone (x : M) (hx : ((1 : P), x) ∈ Γ) : x = 1 := by
    by_contra hne
    obtain ⟨A, B, hA, hB, hxA, h1B, hAB⟩ := t2_separation hne
    obtain ⟨U, hU, hUB⟩ := hf B (hB.mem_nhds h1B)
    obtain ⟨_, ⟨hpU, hpA⟩, w, rfl⟩ :=
      mem_closure_iff_nhds.1 hx (U ×ˢ A) (prod_mem_nhds hU (hA.mem_nhds hxA))
    exact hAB.ne_of_mem hpA (hUB w hpU) rfl
  -- the projection of `Γ` to `P` is surjective
  have hsurj (p : P) : ∃ x, (p, x) ∈ Γ := by
    have hsub : Set.range ι ⊆ Prod.fst '' (Γ : Set (P × M)) :=
      fun _ ⟨w, hw⟩ ↦ ⟨_, hgr w, hw⟩
    have := closure_minimal hsub (hΓc.isCompact.image continuous_fst).isClosed
    rw [hι.closure_range] at this
    obtain ⟨⟨q, x⟩, hx, rfl⟩ := this (Set.mem_univ p)
    exact ⟨x, hx⟩
  -- and injective
  have hinj (p : P) (x y : M) (hx : (p, x) ∈ Γ) (hy : (p, y) ∈ Γ) : x = y := by
    obtain ⟨z, hz⟩ := hsurj p⁻¹
    have h₁ : z * y = 1 := hone _ (by simpa using Γ.mul_mem hz hy)
    have h₂ : x * z = 1 := hone _ (by simpa using Γ.mul_mem hx hz)
    calc x = x * (z * y) := by rw [h₁, mul_one]
      _ = x * z * y := (mul_assoc _ _ _).symm
      _ = y := by rw [h₂, one_mul]
  have hbij : Function.Bijective fun q : Γ ↦ (q : P × M).1 := by
    refine ⟨?_, fun p ↦ ?_⟩
    · rintro ⟨⟨a, x⟩, hx⟩ ⟨⟨b, y⟩, hy⟩ (rfl : a = b)
      obtain rfl := hinj a x y hx hy
      rfl
    · obtain ⟨x, hx⟩ := hsurj p
      exact ⟨⟨(p, x), hx⟩, rfl⟩
  have : CompactSpace Γ := isCompact_iff_compactSpace.1 hΓc.isCompact
  let h : Γ ≃ₜ P := (continuous_fst.comp continuous_subtype_val).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ hbij)
  have hF (p : P) : (p, ((h.symm p : Γ) : P × M).2) ∈ Γ := by
    have hp : ((h.symm p : Γ) : P × M).1 = p := h.apply_symm_apply p
    have := (h.symm p).2
    rwa [← Prod.mk.eta (p := (h.symm p : P × M)), hp] at this
  have hFuniq (p : P) (x : M) (hx : (p, x) ∈ Γ) : ((h.symm p : Γ) : P × M).2 = x :=
    hinj p _ _ (hF p) hx
  refine ⟨{ toFun := fun p ↦ ((h.symm p : Γ) : P × M).2
            map_one' := hFuniq 1 1 Γ.one_mem
            map_mul' := fun p q ↦ hFuniq _ _ (by simpa using Γ.mul_mem (hF p) (hF q)) },
    ?_, fun w ↦ hFuniq _ _ (hgr w)⟩
  exact continuous_snd.comp (continuous_subtype_val.comp h.symm.continuous)

end MonoidHom

namespace PadicInt

/-- The structure map `ℤ_ℓ → ℚ̄_ℓ` is continuous. -/
theorem continuous_algebraMap_padicAlgCl (ℓ : ℕ) [Fact ℓ.Prime] :
    Continuous (algebraMap ℤ_[ℓ] (PadicAlgCl ℓ)) := by
  have : (algebraMap ℤ_[ℓ] (PadicAlgCl ℓ) : ℤ_[ℓ] → PadicAlgCl ℓ) =
      algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) ∘ ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) :=
    funext fun x ↦ IsScalarTower.algebraMap_apply ℤ_[ℓ] ℚ_[ℓ] (PadicAlgCl ℓ) x
  rw [this]
  exact (continuous_algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).comp continuous_subtype_val

/-- A family of `p`-adic matrices tends to `1` as soon as, for every `k`, its reductions modulo
`pᵏ` are eventually `1`. -/
theorem tendsto_one_of_forall_eventually_map_toZModPow {p : ℕ} [Fact p.Prime] {α n : Type*}
    [DecidableEq n] {l : Filter α} {g : α → Matrix n n ℤ_[p]}
    (h : ∀ k, ∀ᶠ x in l, (g x).map (toZModPow k) = 1) : Filter.Tendsto g l (𝓝 1) := by
  refine tendsto_pi_nhds.2 fun a ↦ tendsto_pi_nhds.2 fun b ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hp : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp)
  filter_upwards [h k] with x hx
  have hx' : toZModPow k (g x a b - (1 : Matrix n n ℤ_[p]) a b) = 0 := by
    have := congrFun (congrFun hx a) b
    rw [Matrix.map_apply] at this
    rw [map_sub, this, Matrix.one_apply, Matrix.one_apply, apply_ite (toZModPow k), map_one,
      map_zero, sub_self]
  rw [← RingHom.mem_ker, ker_toZModPow, ← norm_le_pow_iff_mem_span_pow] at hx'
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ hk
  simpa [zpow_neg, inv_pow] using hx'

end PadicInt

namespace Module.Basis

/-- A vector of a lattice `L ⊆ V` in terms of the image of a basis `e` of `L`: for a
`ℤ_ℓ`-semilinear map `j : L → V`, `j x = ∑ᵢ eᵢ*(x) j(eᵢ)`. -/
theorem apply_eq_sum_repr_smul {ℓ : ℕ} [Fact ℓ.Prime] {ι L V : Type*} [Fintype ι]
    [AddCommGroup L] [Module ℤ_[ℓ] L] [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (e : Basis ι ℤ_[ℓ] L) {j : L →+ V}
    (hjs : ∀ (a : ℤ_[ℓ]) x, j (a • x) = algebraMap ℤ_[ℓ] (PadicAlgCl ℓ) a • j x) (x : L) :
    j x = ∑ i, algebraMap ℤ_[ℓ] (PadicAlgCl ℓ) (e.repr x i) • j (e i) := by
  conv_lhs => rw [← e.sum_repr x]
  rw [map_sum]
  simp only [hjs]

/-- **Lattice coordinates are continuous.** Let `j : L → V` be an injective `ℤ_ℓ`-semilinear map
from a `ℤ_ℓ`-module with a finite basis `e` to a finite-dimensional `ℚ̄_ℓ`-vector space. If the
coordinates of `x ↦ j (h x)` are continuous, so are the coordinates of `h` in the basis `e`:
in coordinates, `j` is a continuous injection from the compact space `ℤ_ℓⁿ`, hence a closed
embedding. -/
theorem continuous_repr_apply_of_continuous {ℓ : ℕ} [Fact ℓ.Prime] {ι L V X : Type*}
    [Finite ι] [AddCommGroup L] [Module ℤ_[ℓ] L] [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    [FiniteDimensional (PadicAlgCl ℓ) V] [TopologicalSpace X] (e : Basis ι ℤ_[ℓ] L)
    {j : L →+ V} (hj : Function.Injective j)
    (hjs : ∀ (a : ℤ_[ℓ]) x, j (a • x) = algebraMap ℤ_[ℓ] (PadicAlgCl ℓ) a • j x) {h : X → L}
    (hh : ∀ φ : Module.Dual (PadicAlgCl ℓ) V, Continuous fun x ↦ φ (j (h x))) (i : ι) :
    Continuous fun x ↦ e.repr (h x) i := by
  have := Fintype.ofFinite ι
  set B := Module.finBasis (PadicAlgCl ℓ) V
  set Ψ : (ι → ℤ_[ℓ]) → (Fin (Module.finrank (PadicAlgCl ℓ) V) → PadicAlgCl ℓ) :=
    fun c ↦ B.equivFun (j (e.equivFun.symm c))
  have hΨ : Continuous Ψ := by
    have hΨ' : Ψ = fun c a ↦
        ∑ i, algebraMap ℤ_[ℓ] (PadicAlgCl ℓ) (c i) * B.equivFun (j (e i)) a := by
      funext c a
      simp [Ψ, Basis.equivFun_symm_apply, map_sum, hjs, Algebra.smul_def]
    rw [hΨ']
    exact continuous_pi fun a ↦ continuous_finsetSum _ fun i _ ↦
      ((PadicInt.continuous_algebraMap_padicAlgCl ℓ).comp (continuous_apply i)).mul
        continuous_const
  have hΨi : Function.Injective Ψ := fun c d hcd ↦
    e.equivFun.symm.injective (hj (B.equivFun.injective hcd))
  have hc : Continuous fun x ↦ e.equivFun (h x) := by
    rw [(hΨ.isClosedEmbedding hΨi).isEmbedding.continuous_iff]
    refine continuous_pi fun a ↦ ?_
    simp only [Ψ, Function.comp_apply, e.equivFun.symm_apply_apply]
    simpa only [Basis.equivFun_apply, Basis.coord_apply] using hh (B.coord a)
  exact (continuous_apply i).comp hc

end Module.Basis

namespace LinearMap

/-- **Descent of an action along a surjection.** If `Φ : U → V` is a surjective linear map and
the endomorphisms `σ p` of `U` preserve `ker Φ`, they induce an action `τ` on `V` with
`τ p ∘ Φ = Φ ∘ σ p`. -/
theorem exists_monoidHom_apply_eq_of_surjective {K U V P : Type*} [Field K] [AddCommGroup U]
    [Module K U] [AddCommGroup V] [Module K V] [Monoid P] (Φ : U →ₗ[K] V)
    (hΦ : Function.Surjective Φ) (σ : P →* Module.End K U)
    (hσ : ∀ p c, Φ c = 0 → Φ (σ p c) = 0) :
    ∃ τ : P →* Module.End K V, ∀ p c, τ p (Φ c) = Φ (σ p c) := by
  obtain ⟨s, hs⟩ := Φ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hΦ)
  have hs' (v : V) : Φ (s v) = v := LinearMap.congr_fun hs v
  have key (p : P) (c : U) : Φ (σ p (s (Φ c))) = Φ (σ p c) := by
    rw [← sub_eq_zero, ← map_sub, ← map_sub]
    exact hσ p _ (by rw [map_sub, hs', sub_self])
  refine ⟨{ toFun := fun p ↦ Φ ∘ₗ σ p ∘ₗ s, map_one' := ?_, map_mul' := fun p q ↦ ?_ },
    fun p c ↦ key p c⟩
  · ext v
    simp [hs']
  · ext v
    simp [key]

end LinearMap

namespace MonoidHom

/-- **Open subgroups of the geometric part are open for the profinite topology.** In the
situation of `Representation.exists_extension_of_isBoundedOn`, let `N` be a subgroup of `W`
whose preimage in the compact group `G` is open and which contains a positive power of the
Frobenius `γ`. Then `N` contains all `w` with `ι w` close to `1`. -/
theorem exists_nhds_one_forall_mem_of_isOpen_preimage {W P G : Type*} [Group W] [Group P]
    [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P] [T2Space P]
    [TotallyDisconnectedSpace P] [Group G] [TopologicalSpace G] [CompactSpace G]
    {deg : W →* Multiplicative ℤ} {γ : W} (hγ : deg γ = Multiplicative.ofAdd 1) (κ : G →* W)
    (hκ : ∀ w, deg w = 1 → ∃ g, κ g = w) (ι : W →* P) (hικ : Continuous (ι.comp κ))
    (hικ' : Function.Injective (ι.comp κ))
    (hdeg : ∀ M : ℕ, 0 < M → ∃ U ∈ 𝓝 (1 : P), ∀ w, ι w ∈ U →
      (M : ℤ) ∣ Multiplicative.toAdd (deg w))
    {N : Subgroup W} (hN : IsOpen (κ ⁻¹' N : Set G)) {m : ℕ} (hm : 0 < m) (hγm : γ ^ m ∈ N) :
    ∃ U ∈ 𝓝 (1 : P), ∀ w, ι w ∈ U → w ∈ N := by
  obtain ⟨O, hO, hOeq⟩ := (hικ.isClosedEmbedding hικ').isInducing.isOpen_iff.1 hN
  have h1O : (1 : P) ∈ O := by
    have : (1 : G) ∈ (ι.comp κ) ⁻¹' O := by
      rw [hOeq]
      simp
    simpa using this
  obtain ⟨U₁, hU₁⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO h1O
  have : U₁.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hm' : 0 < U₁.toSubgroup.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hγU₁ : ι γ ^ U₁.toSubgroup.index ∈ U₁.toSubgroup := Subgroup.pow_index_mem _ _
  obtain ⟨U₂, hU₂, hdvd⟩ := hdeg (m * U₁.toSubgroup.index) (Nat.mul_pos hm hm')
  refine ⟨(U₁ : Set P) ∩ U₂, Filter.inter_mem (U₁.isOpen.mem_nhds (one_mem U₁)) hU₂,
    fun w hw ↦ ?_⟩
  obtain ⟨t, ht⟩ := hdvd w hw.2
  push_cast at ht
  obtain ⟨g, hg⟩ := hκ (w * γ ^ (-Multiplicative.toAdd (deg w)))
    (MonoidHom.mem_ker.1 (Representation.mul_zpow_neg_mem_ker hγ w))
  have hγn : ι γ ^ Multiplicative.toAdd (deg w) ∈ U₁ := by
    rw [ht, mul_comm (m : ℤ), mul_assoc, zpow_mul, zpow_natCast]
    exact zpow_mem (hγU₁ : ι γ ^ U₁.toSubgroup.index ∈ U₁) _
  have hg' : κ g ∈ N := by
    have : g ∈ (ι.comp κ) ⁻¹' O := by
      refine hU₁ ?_
      rw [MonoidHom.coe_comp, Function.comp_apply, hg, map_mul, map_zpow, zpow_neg]
      exact mul_mem hw.1 (inv_mem hγn)
    rwa [hOeq] at this
  have hw' : w = κ g * γ ^ Multiplicative.toAdd (deg w) := by
    rw [hg]
    group
  rw [hw']
  refine mul_mem hg' ?_
  rw [ht, mul_assoc, zpow_mul, zpow_natCast]
  exact zpow_mem hγm _

end MonoidHom

namespace Representation

/-- **Bounded representations of a dense Weil group extend to the profinite group** (Deligne,
Weil II, 1.3.14 and 1.1.7). Let `ι : W →* Π` have dense range in a profinite group `Π`, let
`deg : W →* ℤ` have an element `γ` of degree one, and let `κ : G →* W` be a homomorphism from a
compact Hausdorff group onto `ker deg` such that `ι ∘ κ` is continuous and injective. Assume
that the degree is continuous for the topology induced by `Π`: for every `M > 0` there is a
neighbourhood `U` of `1` such that `M ∣ deg w` whenever `ι w ∈ U`. Then every finite-dimensional
representation `ρ` of `W` over `ℚ̄_ℓ` which is continuous along `κ` and bounded on `W` extends to a
continuous representation `τ` of `Π`: `τ ∘ ι = ρ`. -/
theorem exists_extension_of_isBoundedOn {ℓ : ℕ} [Fact ℓ.Prime] {W P G V : Type*} [Group W]
    [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P] [T2Space P]
    [TotallyDisconnectedSpace P] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    [FiniteDimensional (PadicAlgCl ℓ) V] {deg : W →* Multiplicative ℤ} {γ : W}
    (hγ : deg γ = Multiplicative.ofAdd 1) (κ : G →* W)
    (hκ : ∀ w, deg w = 1 → ∃ g, κ g = w) (ι : W →* P) (hι : DenseRange ι)
    (hικ : Continuous (ι.comp κ)) (hικ' : Function.Injective (ι.comp κ))
    (hdeg : ∀ M : ℕ, 0 < M → ∃ U ∈ 𝓝 (1 : P), ∀ w, ι w ∈ U →
      (M : ℤ) ∣ Multiplicative.toAdd (deg w))
    (ρ : Representation (PadicAlgCl ℓ) W V) (hcont : ρ.IsContinuousOn κ)
    (hb : ρ.IsBoundedOn Set.univ) :
    ∃ τ : Representation (PadicAlgCl ℓ) P V, (∀ w, τ (ι w) = ρ w) ∧
      ∀ (φ : Module.Dual (PadicAlgCl ℓ) V) (v : V), Continuous fun x ↦ φ (τ x v) := by
  classical
  -- Step 1: a `W`-stable lattice `L`
  let ρ' : W →* (V ≃ₗ[PadicAlgCl ℓ] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ V).toMonoidHom.comp ρ.asGroupHom
  have hρ' (w : W) (v : V) : ρ' w v = ρ w v := rfl
  have hgen : Subgroup.closure (Set.range κ ∪ {γ}) = ⊤ := by
    refine (Subgroup.eq_top_iff' _).2 fun w ↦ ?_
    obtain ⟨g, hg⟩ := hκ _ (MonoidHom.mem_ker.1 (Representation.mul_zpow_neg_mem_ker hγ w))
    have h₁ : κ g ∈ Subgroup.closure (Set.range κ ∪ {γ}) :=
      Subgroup.subset_closure (Or.inl ⟨g, rfl⟩)
    have h₂ : γ ∈ Subgroup.closure (Set.range κ ∪ {γ}) := Subgroup.subset_closure (Or.inr rfl)
    simpa [hg] using mul_mem h₁ (Subgroup.zpow_mem _ h₂ (Multiplicative.toAdd (deg w)))
  obtain ⟨L, _, _, _, _, ρL, j, hj, hjs, hjρ, hspan⟩ :=
    MonoidHom.exists_lattice_of_isWeaklyBounded_of_compactSpace ρ' κ (Set.finite_singleton γ)
      hgen (fun v φ ↦ hcont φ v) fun v ↦ by simpa [hρ', Set.image_univ] using hb v
  set e := Module.finBasis ℤ_[ℓ] L
  -- Step 2: the matrices of `ρ_L` and their continuity on `G`
  let f : W →* Matrix (Fin (Module.finrank ℤ_[ℓ] L)) (Fin (Module.finrank ℤ_[ℓ] L)) ℤ_[ℓ] :=
    (LinearMap.toMatrixAlgEquiv e).toMonoidHom.comp
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρL)
  have hf (w : W) (a b) : f w a b = e.repr (ρL w (e b)) a := by
    simp [f, LinearMap.toMatrixAlgEquiv_apply]
  have hfκ : Continuous fun g ↦ f (κ g) := by
    refine continuous_pi fun a ↦ continuous_pi fun b ↦ ?_
    simp_rw [hf]
    refine e.continuous_repr_apply_of_continuous hj hjs (fun φ ↦ ?_) a
    simp_rw [hjρ, hρ']
    exact hcont φ (j (e b))
  -- Step 3: the reductions modulo `ℓᵏ` are continuous for the topology of `P`
  have hred (k : ℕ) : ∃ U ∈ 𝓝 (1 : P), ∀ w, ι w ∈ U → (f w).map (PadicInt.toZModPow k) = 1 := by
    let fk := ((PadicInt.toZModPow (p := ℓ) k).mapMatrix.toMonoidHom.comp f).toHomUnits
    have hN (w : W) : w ∈ fk.ker ↔ (f w).map (PadicInt.toZModPow k) = 1 := by
      rw [MonoidHom.mem_ker, Units.ext_iff, MonoidHom.coe_toHomUnits, Units.val_one]
      rfl
    have hopen : IsOpen (κ ⁻¹' (fk.ker : Set W)) := by
      have : κ ⁻¹' (fk.ker : Set W) =
          (fun g ↦ (f (κ g)).map (PadicInt.toZModPow k)) ⁻¹' {1} := by
        ext g
        simp [hN]
      rw [this]
      exact (isOpen_discrete _).preimage (hfκ.matrix_map (PadicInt.continuous_toZModPow k))
    have : NeZero (ℓ ^ k) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
    have hfin := isOfFinOrder_of_finite (fk γ)
    obtain ⟨U, hU, hUN⟩ := MonoidHom.exists_nhds_one_forall_mem_of_isOpen_preimage hγ κ hκ ι
      hικ hικ' hdeg hopen hfin.orderOf_pos (by rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one])
    exact ⟨U, hU, fun w hw ↦ (hN w).1 (hUN w hw)⟩
  -- Step 4: extension of `f` to `P` (closed graph)
  have : CompactSpace
      (Matrix (Fin (Module.finrank ℤ_[ℓ] L)) (Fin (Module.finrank ℤ_[ℓ] L)) ℤ_[ℓ]) :=
    inferInstanceAs (CompactSpace (Fin _ → Fin _ → ℤ_[ℓ]))
  have htend : Filter.Tendsto f (Filter.comap ι (𝓝 1)) (𝓝 1) :=
    PadicInt.tendsto_one_of_forall_eventually_map_toZModPow fun k ↦ by
      obtain ⟨U, hU, hUf⟩ := hred k
      exact Filter.mem_comap.2 ⟨U, hU, fun w hw ↦ hUf w hw⟩
  obtain ⟨F, hFc, hFι⟩ := MonoidHom.exists_continuous_extend_of_forall_nhds_one ι hι f
    fun V hV ↦ by
      obtain ⟨U, hU, hUV⟩ := Filter.mem_comap.1 (htend hV)
      exact ⟨U, hU, fun w hw ↦ hUV hw⟩
  -- Step 5: descent of the matrix action from `ℚ̄_ℓⁿ` to `V`
  let Φ : (Fin (Module.finrank ℤ_[ℓ] L) → PadicAlgCl ℓ) →ₗ[PadicAlgCl ℓ] V :=
    Fintype.linearCombination (PadicAlgCl ℓ) fun i ↦ j (e i)
  have hΦ (c) : Φ c = ∑ i, c i • j (e i) := by
    simp [Φ, Fintype.linearCombination_apply]
  let σ : P →* Module.End (PadicAlgCl ℓ) (Fin (Module.finrank ℤ_[ℓ] L) → PadicAlgCl ℓ) :=
    (Matrix.toLinAlgEquiv' : _ ≃ₐ[PadicAlgCl ℓ] _).toMonoidHom.comp
      ((algebraMap ℤ_[ℓ] (PadicAlgCl ℓ)).mapMatrix.toMonoidHom.comp F)
  have hσ (p : P) (c) : σ p c = ((F p).map (algebraMap ℤ_[ℓ] (PadicAlgCl ℓ))).mulVec c := by
    simp [σ, Matrix.toLinAlgEquiv'_apply]
  have hΦσ (w : W) (c) : Φ (σ (ι w) c) = ρ w (Φ c) := by
    simp_rw [hσ, hFι, hΦ, map_sum, map_smul, ← hρ', ← hjρ,
      e.apply_eq_sum_repr_smul hjs (ρL w (e _)), Finset.smul_sum, smul_smul, Matrix.mulVec,
      dotProduct, Finset.sum_smul, Matrix.map_apply, hf]
    rw [Finset.sum_comm]
    simp [mul_comm]
  have hΦsurj : Function.Surjective Φ := by
    refine LinearMap.range_eq_top.1 (eq_top_iff.2 (hspan ▸ Submodule.span_le.2 ?_))
    rintro _ ⟨x, rfl⟩
    exact ⟨_, by rw [hΦ, e.apply_eq_sum_repr_smul hjs x]⟩
  have hcontσ (φ : Module.Dual (PadicAlgCl ℓ) V) (c) : Continuous fun p ↦ φ (Φ (σ p c)) := by
    simp_rw [hσ]
    exact (LinearMap.continuous_on_pi (φ ∘ₗ Φ)).comp
      ((hFc.matrix_map (PadicInt.continuous_algebraMap_padicAlgCl ℓ)).matrix_mulVec
        continuous_const)
  have hσker (p : P) (c) (hc : Φ c = 0) : Φ (σ p c) = 0 := by
    rw [← Module.forall_dual_apply_eq_zero_iff (PadicAlgCl ℓ)]
    intro φ
    have := hι.equalizer (hcontσ φ c) (continuous_const (y := (0 : PadicAlgCl ℓ)))
      (funext fun w ↦ by simp [hΦσ, hc])
    exact congrFun this p
  obtain ⟨τ, hτ⟩ := Φ.exists_monoidHom_apply_eq_of_surjective hΦsurj σ hσker
  refine ⟨τ, fun w ↦ LinearMap.ext fun v ↦ ?_, fun φ v ↦ ?_⟩
  · obtain ⟨c, rfl⟩ := hΦsurj v
    rw [hτ, hΦσ]
  · obtain ⟨c, rfl⟩ := hΦsurj v
    simp_rw [hτ]
    exact hcontσ φ c

end Representation
