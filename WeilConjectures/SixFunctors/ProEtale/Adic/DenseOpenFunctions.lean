/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheaf

/-!
# Extending locally finite `ℓ`-adic functions over a dense open

Let `e : T' ⟶ T` be an open embedding of topological spaces. Suppose that every point of `T` is
a specialization of a point of the image of `e`, that any two generizations of a point of `T`
have a common generization, that closures of relatively clopen subsets of the image are
detected by specializations, and that `T` is covered by opens whose preimages in `T'` are
compact. Then restriction along `e` is a bijection between the locally finite continuous
`ℓ`-adic functions on `T` and on `T'`
(`PadicAlgCl.bijective_locallyFiniteFunctionsComp_of_isOpenEmbedding`).

Uniqueness holds because continuous functions to the Hausdorff space `ℚ̄_ℓ` are constant along
specializations. The extension of `g` takes at `x` the value of `g` at any generization of `x`
in `T'`, which is well defined by the second hypothesis. It is continuous since the
`ℓ`-adic balls are clopen, `ℚ̄_ℓ` being ultrametric: the points of `T'` at which `g` is far
from its value at `x` form a relatively clopen set whose closure does not contain `x`.
-/

@[expose] public section

open Topology

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {T T' : Type*} [TopologicalSpace T] [TopologicalSpace T']

/-- The values of a locally finite function on a compact set span a finite-dimensional
`ℚ_ℓ`-subspace. -/
lemma finiteDimensional_span_image_of_isCompact {f : C(T, PadicAlgCl l)}
    (hf : f ∈ locallyFiniteFunctions l T) {K : Set T} (hK : IsCompact K) :
    FiniteDimensional ℚ_[l] (Submodule.span ℚ_[l] (f '' K)) := by
  choose U hU hfin using hf
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover U (fun x _ ↦ hU x)
  refine Submodule.finiteDimensional_of_le (S₂ := t.sup fun x ↦ Submodule.span ℚ_[l] (f '' U x))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
  exact Finset.le_sup (f := fun x ↦ Submodule.span ℚ_[l] (f '' U x)) hx
    (Submodule.subset_span ⟨y, hyx, rfl⟩)

omit [TopologicalSpace T'] in
/-- Two continuous `ℓ`-adic functions agreeing on a set of points which generize every point
agree. -/
lemma eq_of_comp_eq_of_forall_specializes {e : T' → T}
    (hgen : ∀ x : T, ∃ y : T', e y ⤳ x) {f₁ f₂ : C(T, PadicAlgCl l)}
    (h : ∀ y, f₁ (e y) = f₂ (e y)) : f₁ = f₂ := by
  ext x
  obtain ⟨y, hy⟩ := hgen x
  rw [← (hy.map f₁.continuous).eq, ← (hy.map f₂.continuous).eq, h]

/-- **Extension of locally finite functions over a dense open.** Let `e : T' ⟶ T` be an open
embedding such that
- every point of `T` is a specialization of a point of the image of `e`;
- any two generizations of a point of `T` have a common generization;
- a point in the closure of the image of a clopen subset `B` of `T'` is a specialization of a
  point of the image of `B`;
- every point of `T` has an open neighbourhood with compact preimage in `T'`.

Then restriction along `e` is a bijection on locally finite continuous `ℓ`-adic functions. -/
theorem bijective_locallyFiniteFunctionsComp_of_isOpenEmbedding (e : C(T', T))
    (he : IsOpenEmbedding e) (hgen : ∀ x : T, ∃ y : T', e y ⤳ x)
    (hdir : ∀ x y₁ y₂ : T, y₁ ⤳ x → y₂ ⤳ x → ∃ z, z ⤳ y₁ ∧ z ⤳ y₂)
    (hcl : ∀ B : Set T', IsClopen B → ∀ x ∈ closure (e '' B), ∃ b ∈ B, e b ⤳ x)
    (hfin : ∀ x : T, ∃ N : Set T, IsOpen N ∧ x ∈ N ∧ IsCompact (e ⁻¹' N)) :
    Function.Bijective (locallyFiniteFunctionsComp l e) := by
  refine ⟨fun f₁ f₂ h ↦ Subtype.ext (eq_of_comp_eq_of_forall_specializes hgen fun y ↦ ?_),
    fun g ↦ ?_⟩
  · exact congrArg (fun f : locallyFiniteFunctions l T' ↦ f.1 y) h
  choose y hy using hgen
  -- `g` is constant on the generizations of a point lying in `T'`
  have key (x : T) (b : T') (hb : e b ⤳ x) : g.1 b = g.1 (y x) := by
    obtain ⟨z, hz₁, hz₂⟩ := hdir x (e b) (e (y x)) hb (hy x)
    obtain ⟨z', rfl⟩ := hz₁.mem_open he.isOpen_range ⟨b, rfl⟩
    rw [he.isInducing.specializes_iff] at hz₁ hz₂
    rw [← (hz₁.map g.1.continuous).eq, ← (hz₂.map g.1.continuous).eq]
  let G : T → PadicAlgCl l := fun x ↦ g.1 (y x)
  have hG : Continuous G := by
    refine continuous_iff_continuousAt.2 fun x ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
    let B : Set T' := g.1 ⁻¹' (Metric.ball (G x) ε)ᶜ
    have hB : IsClopen B := (IsUltrametricDist.isClopen_ball (G x) ε).compl.preimage g.1.continuous
    have hx : x ∉ closure (e '' B) := fun hx ↦ by
      obtain ⟨b, hb, hbx⟩ := hcl B hB x hx
      exact hb (by rw [key x b hbx]; exact Metric.mem_ball_self hε)
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with z hz
    by_contra hzB
    exact hz (closure_mono (s := {e (y z)})
      (Set.singleton_subset_iff.2 (⟨y z, hzB, rfl⟩ : e (y z) ∈ e '' B))
      (specializes_iff_mem_closure.1 (hy z)))
  refine ⟨⟨⟨G, hG⟩, fun x ↦ ?_⟩, Subtype.ext (ContinuousMap.ext fun b ↦ (key (e b) b le_rfl).symm)⟩
  obtain ⟨N, hN, hxN, hNc⟩ := hfin x
  have := finiteDimensional_span_image_of_isCompact g.2 hNc
  refine ⟨N, hN.mem_nhds hxN, Submodule.finiteDimensional_of_le
    (S₂ := Submodule.span ℚ_[l] (g.1 '' (e ⁻¹' N))) (Submodule.span_mono ?_)⟩
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨y z, (hy z).mem_open hN hz, rfl⟩

end PadicAlgCl
