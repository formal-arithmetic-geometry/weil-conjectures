module

public import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Valuation topologies and common nontrivial coarsenings

Source: ILO, Travaux de Gabber, XX 4.4, printed pp.373–374, valued-field background.
The criterion is the elementary reconstruction recorded in the DAG, rather than a theorem
quoted from ILO; Bourbaki, Commutative Algebra VI §§4,8 is listed as wanted.
(blueprint: lem-per-valuation-topology-common-coarsening)
-/

@[expose] public section

universe u v w

section

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

variable {K : Type u} [Field K]
variable {G : Type v} [LinearOrderedCommGroupWithZero G]
variable {H : Type w} [LinearOrderedCommGroupWithZero H]

private theorem valuation_mem_nhds (v : Valuation K G) (x : K) (s : Set K) :
    s ∈ @nhds K v.subgroups_basis.topology x ↔
      ∃ a : Kˣ, ∀ y : K, v (y - x) < v (a : K) → y ∈ s := by
  rw [v.subgroups_basis.hasBasis_nhds x |>.mem_iff]
  constructor
  · rintro ⟨γ, _, hγ⟩
    obtain ⟨a, ha⟩ := restrict₀_surjective (.ofClass v) γ.val
    have ha0 : a ≠ 0 := by
      intro h
      subst a
      apply γ.ne_zero
      simpa using ha.symm
    refine ⟨Units.mk0 a ha0, ?_⟩
    intro y hy
    apply hγ
    change v (y - x) < embedding γ.val
    simpa only [← ha, embedding_restrict₀, MonoidWithZeroHom.coe_ofClass,
      Units.val_mk0] using hy
  · rintro ⟨a, ha⟩
    let γ : (ValueGroup₀ (.ofClass v))ˣ :=
      Units.mk0 (v.restrict (a : K)) (by simp)
    refine ⟨γ, trivial, ?_⟩
    intro y hy
    apply ha
    change v (y - x) < embedding γ.val at hy
    simpa only [γ, Units.val_mk0, Valuation.embedding_restrict] using hy

private theorem valuation_topology_eq (v : Valuation K G) (w : Valuation K H)
    (hvw : ∀ a : Kˣ, ∃ b : Kˣ, ∀ x : K, w x < w (b : K) → v x < v (a : K))
    (hwv : ∀ b : Kˣ, ∃ a : Kˣ, ∀ x : K, v x < v (a : K) → w x < w (b : K)) :
    v.subgroups_basis.topology = w.subgroups_basis.topology := by
  apply TopologicalSpace.ext_nhds
  intro x
  apply Filter.ext
  intro s
  rw [valuation_mem_nhds, valuation_mem_nhds]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := hvw a
    exact ⟨b, fun y hy ↦ ha y (hb (y - x) hy)⟩
  · rintro ⟨b, hb⟩
    obtain ⟨a, ha⟩ := hwv b
    exact ⟨a, fun y hy ↦ hb y (ha (y - x) hy)⟩

private theorem closure_valuation_bound (v : Valuation K G) (w : Valuation K H)
    {x : K} (hx : x ∈ Subring.closure
      ((v.valuationSubring : Set K) ∪ (w.valuationSubring : Set K))) :
    ∃ b : K, b ∈ w.valuationSubring ∧ v x ≤ v b := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨1, w.valuationSubring.one_mem, by simpa using hx⟩
    · exact ⟨x, hx, le_rfl⟩
  | zero => exact ⟨0, w.valuationSubring.zero_mem, le_rfl⟩
  | one => exact ⟨1, w.valuationSubring.one_mem, le_rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, hxb⟩ := hx
    obtain ⟨c, hc, hyc⟩ := hy
    rcases le_total (v b) (v c) with hbc | hcb
    · exact ⟨c, hc, (v.map_add x y).trans (max_le (hxb.trans hbc) hyc)⟩
    · exact ⟨b, hb, (v.map_add x y).trans (max_le hxb (hyc.trans hcb))⟩
  | neg x _ hx =>
    obtain ⟨b, hb, hxb⟩ := hx
    exact ⟨b, hb, by simpa using hxb⟩
  | mul x y _ _ hx hy =>
    obtain ⟨b, hb, hxb⟩ := hx
    obtain ⟨c, hc, hyc⟩ := hy
    refine ⟨b * c, w.valuationSubring.mul_mem _ _ hb hc, ?_⟩
    simpa only [map_mul] using mul_le_mul' hxb hyc

private theorem common_coarsening_of_topology_eq
    (v : Valuation K G) (w : Valuation K H) [v.IsNontrivial]
    (h : v.subgroups_basis.topology = w.subgroups_basis.topology) :
    ∃ U : ValuationSubring K, U ≠ ⊤ ∧ v.valuationSubring ≤ U ∧ w.valuationSubring ≤ U := by
  have hn : {x : K | w x < 1} ∈ @nhds K w.subgroups_basis.topology 0 := by
    rw [valuation_mem_nhds]
    exact ⟨1, by simp⟩
  rw [← h] at hn
  obtain ⟨a, ha⟩ := (valuation_mem_nhds v 0 _).mp hn
  have hbound : ∀ b : K, b ∈ w.valuationSubring → v b ≤ (v (a : K))⁻¹ := by
    intro b hb
    by_contra hb'
    have hlt : (v (a : K))⁻¹ < v b := lt_of_not_ge hb'
    have hb0 : b ≠ 0 := by
      intro hb0
      simp [hb0] at hlt
    have hva : 0 < v (a : K) := v.pos_iff.mpr a.ne_zero
    have hvb : 0 < v b := v.pos_iff.mpr hb0
    have hbinv : v b⁻¹ < v (a : K) := by
      rw [map_inv₀]
      exact (inv_lt_comm₀ hva hvb).mp hlt
    have hwbinv : w b⁻¹ < 1 := ha b⁻¹ (by simpa using hbinv)
    have : 1 < w b := (w.one_lt_val_iff hb0).mpr hwbinv
    exact this.not_ge hb
  let S : Subring K := Subring.closure
    ((v.valuationSubring : Set K) ∪ (w.valuationSubring : Set K))
  have hvS : v.valuationSubring.toSubring ≤ S :=
    fun x hx ↦ Subring.subset_closure (Or.inl hx)
  have hwS : w.valuationSubring.toSubring ≤ S :=
    fun x hx ↦ Subring.subset_closure (Or.inr hx)
  let U : ValuationSubring K :=
    { S with
      mem_or_inv_mem' := by
        intro x
        exact (v.valuationSubring.mem_or_inv_mem x).imp
          (fun hx ↦ hvS hx) (fun hx ↦ hvS hx) }
  refine ⟨U, ?_, hvS, hwS⟩
  obtain ⟨d, hd⟩ := Valuation.IsNontrivial.exists_one_lt (v := v)
  have hy : (v (a : K))⁻¹ < v ((a : K)⁻¹ * d) := by
    rw [map_mul, map_inv₀]
    exact lt_mul_of_one_lt_right (inv_pos.mpr (v.pos_iff.mpr a.ne_zero)) hd
  intro hU
  have hyU : (a : K)⁻¹ * d ∈ U := hU.symm ▸ ValuationSubring.mem_top _
  obtain ⟨b, hb, hyb⟩ := closure_valuation_bound v w hyU
  exact hy.not_ge (hyb.trans (hbound b hb))

private theorem coarsening_ball_refinement
    (v : Valuation K G) (w : Valuation K H) [v.IsNontrivial]
    (U : ValuationSubring K) (hU : U ≠ ⊤)
    (hv : v.valuationSubring ≤ U) (hw : w.valuationSubring ≤ U) (a : Kˣ) :
    ∃ b : Kˣ, ∀ x : K, w x < w (b : K) → v x < v (a : K) := by
  have hz : ∃ z : K, z ∉ U := by
    by_contra hz
    apply hU
    apply ValuationSubring.ext
    simp_all
  obtain ⟨z, hz⟩ := hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hz U.zero_mem
  have htU : ∀ u : K, u ∈ U → z⁻¹ * u ∈ v.valuationSubring := by
    intro u hu
    by_contra htu
    have hi : (z⁻¹ * u)⁻¹ ∈ v.valuationSubring :=
      (v.valuationSubring.mem_or_inv_mem _).resolve_left htu
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact htu (by simp)
    apply hz
    have heq : u * (z⁻¹ * u)⁻¹ = z := by
      simp [mul_inv_rev, hu0]
    rw [← heq]
    exact U.mul_mem _ _ hu (hv hi)
  obtain ⟨d, hd0, hd⟩ := Valuation.IsNontrivial.exists_lt_one (v := v)
  let c : Kˣ := a * Units.mk0 d hd0
  let b : Kˣ := c * (Units.mk0 z hz0)⁻¹
  refine ⟨b, ?_⟩
  intro x hx
  have hxb : x / (b : K) ∈ w.valuationSubring := by
    change w (x / (b : K)) ≤ 1
    rw [map_div₀]
    exact (div_lt_one₀ (w.pos_iff.mpr b.ne_zero)).mpr hx |>.le
  have ht : z⁻¹ * (x / (b : K)) ∈ v.valuationSubring := htU _ (hw hxb)
  have heq : x = (c : K) * (z⁻¹ * (x / (b : K))) := by
    change x = (c : K) * (z⁻¹ * (x / ((c : K) * z⁻¹)))
    field_simp
  calc
    v x = v (c : K) * v (z⁻¹ * (x / (b : K))) := by rw [← map_mul, ← heq]
    _ ≤ v (c : K) := by simpa using mul_le_mul' (le_refl (v (c : K))) ht
    _ < v (a : K) := by
      change v ((a : K) * d) < v (a : K)
      rw [map_mul]
      exact mul_lt_of_lt_one_right (v.pos_iff.mpr a.ne_zero) hd

end

namespace AddValuation

/-- Two nontrivial additive valuations with surjective value groups induce the same topology
exactly when their valuation rings lie in a common proper valuation subring of the field.
The topology is Mathlib's subgroup-basis topology of `toValuation`: reversing the value
order turns its strict multiplicative balls into the strict additive balls in the node.

Source: ILO XX 4.4, printed pp.373–374, background only; the following proof is the
agent reconstruction in the DAG (blueprint: lem-per-valuation-topology-common-coarsening).

Proof plan:
1. The valuation identities give v(1) = v(-1) = 0 and v(x⁻¹) = -v(x) for x nonzero.
   Thus V_i = {x | 0 ≤ v_i(x)} is a valuation subring with fraction field K, by
   def-trf-valuation-ring. A ball containing zero is a zero-centered ball; translations
   carry balls to balls.
2. If the topologies agree, choose B₁(δ) ⊆ B₂(0). Nontriviality gives ε > 0; put
   α = max(δ, 0) + ε. For nonzero b in V₂, v₁(b) < -α would put b⁻¹ in B₂(0),
   contrary to v₂(b) ≥ 0. Hence v₁(b) ≥ -α for all b in V₂, including zero.
3. Let U be the finite sums of products ab with a in V₁ and b in V₂. Concatenation,
   negation and distributivity make U a subring containing both. Each product has value
   at least -α, so induction using the ultrametric inequality gives this bound on U.
4. Surjectivity supplies y with v₁(y) = -2α, so U is proper. Since U contains V₁,
   every nonzero x or its inverse belongs to U and K is its fraction field. Thus U is
   a valuation ring, by def-trf-valuation-ring.
5. Conversely, choose z outside a common proper valuation subring U and put t = z⁻¹.
   Then t belongs to U and tU ⊆ V_i: otherwise for u in U with tu outside V_i,
   (tu)⁻¹ belongs to V_i ⊆ U, forcing z = u(tu)⁻¹ into U, a contradiction.
6. For i ≠ j and γ in Γ_i choose a nonzero a with v_i(a) > γ, using nontriviality
   and surjectivity. Then B_j(v_j(at)) ⊆ atV_j ⊆ atU ⊆ aV_i ⊆ B_i(γ).
   These inclusions in both directions identify the zero-neighbourhood filters.
   Translation of balls identifies the topologies. No rank, henselianity or completeness
   hypothesis is used. -/
theorem topology_eq_iff_exists_common_proper_coarsening
    {K : Type u} [Field K]
    {Γ₁ : Type v} [AddCommGroup Γ₁] [LinearOrder Γ₁] [IsOrderedAddMonoid Γ₁]
    {Γ₂ : Type w} [AddCommGroup Γ₂] [LinearOrder Γ₂] [IsOrderedAddMonoid Γ₂]
    (v₁ : AddValuation K (WithTop Γ₁)) (v₂ : AddValuation K (WithTop Γ₂))
    (h₁ : ∃ x : Kˣ, v₁ (x : K) ≠ 0) (h₂ : ∃ x : Kˣ, v₂ (x : K) ≠ 0)
    (hs₁ : ∀ γ : Γ₁, ∃ x : Kˣ, v₁ (x : K) = (γ : WithTop Γ₁))
    (hs₂ : ∀ γ : Γ₂, ∃ x : Kˣ, v₂ (x : K) = (γ : WithTop Γ₂)) :
    v₁.toValuation.subgroups_basis.topology = v₂.toValuation.subgroups_basis.topology ↔
      ∃ U : ValuationSubring K, U ≠ ⊤ ∧
        v₁.toValuation.valuationSubring ≤ U ∧ v₂.toValuation.valuationSubring ≤ U := by
  have _ := hs₁
  have _ := hs₂
  have hv₁ : v₁.toValuation.IsNontrivial := by
    rw [Valuation.isNontrivial_iff_exists_unit]
    obtain ⟨x, hx⟩ := h₁
    exact ⟨x, hx⟩
  let := hv₁
  have hv₂ : v₂.toValuation.IsNontrivial := by
    rw [Valuation.isNontrivial_iff_exists_unit]
    obtain ⟨x, hx⟩ := h₂
    exact ⟨x, hx⟩
  let := hv₂
  constructor
  · exact common_coarsening_of_topology_eq v₁.toValuation v₂.toValuation
  · rintro ⟨U, hU, hv, hw⟩
    exact valuation_topology_eq v₁.toValuation v₂.toValuation
      (coarsening_ball_refinement v₁.toValuation v₂.toValuation U hU hv hw)
      (coarsening_ball_refinement v₂.toValuation v₁.toValuation U hU hw hv)

end AddValuation
