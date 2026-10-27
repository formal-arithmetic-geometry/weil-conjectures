/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Data.NNReal.Basic
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Zorn

/-! # Bounded extensions from local extendability

Source: Weil blueprint, sec-six-functors-basics,
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), agent scalar-extension
expansion, old steps 5--6 (blueprint: lem-sfb-bounded-extension-zorn).
The graph argument is an agent-written expansion, absent from the blueprint itself.

## Main definitions

- `LinearMap.boundedExtensionGraphs`: the set of graphs specified by the node.

## Main statements

- `LinearMap.bounded_extension_zorn`: chain unions, maximal graphs, and a global extension.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped NNReal

namespace LinearMap

/-- The family of graphs of all linear extensions of `f` with the fixed bound `C`.
The graph is Mathlib's `LinearPMap.graph`, viewed as a set in `V × K`; its members
are exactly the pairs `(u, g u)` for `u` in the domain submodule.

Source: agent scalar-extension expansion, old steps 5--6, attached to paragraph (3)
of the Weil blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`
(blueprint: lem-sfb-bounded-extension-zorn). This is the family explicitly specified
in the node, rather than a choice of a partial extension. -/
def boundedExtensionGraphs
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    (abv : AbsoluteValue K ℝ≥0) (ν : V → ℝ≥0) (C : ℝ)
    (W : Submodule K V) (f : W →ₗ[K] K) : Set (Set (V × K)) :=
  {A | ∃ (U : Submodule K V) (hWU : W ≤ U) (g : U →ₗ[K] K),
    g.comp (Submodule.inclusion hWU) = f ∧
    (∀ u : U, (abv (g u) : ℝ) ≤ C * (ν (u : V) : ℝ)) ∧
    A = ((LinearPMap.mk U g).graph : Set (V × K))}

-- The conditional Zorn argument needs only the bounds and local extendability.
set_option linter.unusedVariables false in
/-- Local bound-preserving one-vector extensions give chain upper bounds, maximal
graphs with full domain, and a bound-preserving global linear extension.

Source: agent scalar-extension expansion, old steps 5--6, attached to paragraph (3)
of the Weil blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`
(blueprint: lem-sfb-bounded-extension-zorn). The argument is absent from the blueprint
itself; the node records its proof origin as agent-written.

Proof:
1. The graph of `f` is in `boundedExtensionGraphs abv ν C W f`, using domain `W`
   and the given bound. Inclusion is a partial order on sets, and this graph is an
   upper bound for the empty chain.
2. For a nonempty chain `c`, put `H = ⋃₀ c`. If `(u,b)` and `(u,d)` lie in `H`,
   choose members containing these pairs. Their comparability puts both pairs in
   one function graph, so `b = d`. Thus `H` is the graph of a function on its
   first-coordinate projection. Nonemptiness ensures that it contains the graph
   of `f`, so this domain contains `W` and the function restricts to `f`.
3. Any two domain elements lie in a common member graph, by comparability.
   Additivity and scalar preservation there show that the union domain is a
   submodule and the union function is linear. Zero belongs to `W`. Each pair
   in `H` inherits the same bound `C` from a member graph. Hence `H` is in the
   family and contains every member of `c`.
4. Apply `zorn_subset` (lem-weil-pbc-zorn-lemma) to this set of subsets of `V × K`.
   Step 1 handles the empty chain, and steps 2--3 handle all nonempty chains.
   It gives a maximal member.
5. For any maximal graph on `U`, if `U` is proper choose `x` outside `U`.
   Local extendability gives a bounded map on `U ⊔ span K {x}` whose graph
   contains the maximal graph. It contains the new pair `(x,G(x))`, since
   `x = 0 + 1 • x`, so the inclusion is strict, a contradiction. Every maximal
   domain is therefore `V`. Its map gives the required global extension, with
   the restriction and bound inherited from membership in the family. -/
theorem bounded_extension_zorn
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    (abv : AbsoluteValue K ℝ≥0) (ν : V → ℝ≥0)
    (hνzero : ∀ v : V, ν v = 0 ↔ v = 0)
    (hνsmul : ∀ (a : K) (v : V), ν (a • v) = abv a * ν v)
    (hνadd : ∀ v w : V, ν (v + w) ≤ ν v + ν w)
    (C : ℝ) (hC : 0 < C) (W : Submodule K V) (f : W →ₗ[K] K)
    (hf : ∀ w : W, (abv (f w) : ℝ) ≤ C * (ν (w : V) : ℝ))
    (hext : ∀ (U : Submodule K V) (hWU : W ≤ U) (g : U →ₗ[K] K),
      g.comp (Submodule.inclusion hWU) = f →
      (∀ u : U, (abv (g u) : ℝ) ≤ C * (ν (u : V) : ℝ)) →
      ∀ x : V, x ∉ U → ∃ G : ↥(U ⊔ Submodule.span K {x}) →ₗ[K] K,
        G.comp (Submodule.inclusion le_sup_left) = g ∧
        ∀ y : ↥(U ⊔ Submodule.span K {x}), (abv (G y) : ℝ) ≤ C * (ν (y : V) : ℝ)) :
    (∀ c : Set (Set (V × K)), c ⊆ boundedExtensionGraphs abv ν C W f →
      IsChain (· ⊆ ·) c → c.Nonempty →
      ⋃₀ c ∈ boundedExtensionGraphs abv ν C W f ∧ ⋃₀ c ∈ upperBounds c) ∧
    (((LinearPMap.mk W f).graph : Set (V × K)) ∈ boundedExtensionGraphs abv ν C W f ∧
      ((LinearPMap.mk W f).graph : Set (V × K)) ∈
        upperBounds (∅ : Set (Set (V × K)))) ∧
    (∃ M : Set (V × K), Maximal (· ∈ boundedExtensionGraphs abv ν C W f) M) ∧
    (∀ M : Set (V × K), Maximal (· ∈ boundedExtensionGraphs abv ν C W f) M →
      Prod.fst '' M = Set.univ) ∧
    (∃ h : V →ₗ[K] K, h.comp W.subtype = f ∧
      ∀ v : V, (abv (h v) : ℝ) ≤ C * (ν v : ℝ)) := by
  classical
  have graph_mono {U T : Submodule K V} (hUT : U ≤ T)
      (g : U →ₗ[K] K) (G : T →ₗ[K] K)
      (hG : G.comp (Submodule.inclusion hUT) = g) :
      ((LinearPMap.mk U g).graph : Set (V × K)) ⊆
        ((LinearPMap.mk T G).graph : Set (V × K)) := by
    intro z hz
    obtain ⟨u, rfl⟩ := (LinearPMap.mem_graph_iff' _).mp hz
    apply (LinearPMap.mem_graph_iff' _).mpr
    refine ⟨Submodule.inclusion hUT u, ?_⟩
    have heq := congrArg (fun k : U →ₗ[K] K ↦ k u) hG
    exact Prod.ext rfl heq
  have base_mem : ((LinearPMap.mk W f).graph : Set (V × K)) ∈
      boundedExtensionGraphs abv ν C W f := by
    refine ⟨W, le_rfl, f, ?_, hf, rfl⟩
    ext w
    rfl
  have chain_bound : ∀ c : Set (Set (V × K)),
      c ⊆ boundedExtensionGraphs abv ν C W f → IsChain (· ⊆ ·) c → c.Nonempty →
      ⋃₀ c ∈ boundedExtensionGraphs abv ν C W f ∧ ⋃₀ c ∈ upperBounds c := by
    intro c hc hchain hne
    have pair_mem : ∀ A ∈ c, ∀ B ∈ c, ∃ D ∈ c, A ⊆ D ∧ B ⊆ D := by
      intro A hA B hB
      rcases hchain.total hA hB with hAB | hBA
      · exact ⟨B, hB, hAB, fun _ h ↦ h⟩
      · exact ⟨A, hA, (fun _ h ↦ h), hBA⟩
    let H : Submodule K (V × K) :=
      { carrier := ⋃₀ c
        zero_mem' := by
          obtain ⟨A, hA⟩ := hne
          obtain ⟨U, hWU, g, hg, hb, rfl⟩ := hc hA
          exact Set.mem_sUnion.mpr ⟨_, hA, (LinearPMap.mk U g).graph.zero_mem⟩
        add_mem' := by
          intro x y hx hy
          obtain ⟨A, hA, hx⟩ := Set.mem_sUnion.mp hx
          obtain ⟨B, hB, hy⟩ := Set.mem_sUnion.mp hy
          obtain ⟨D, hD, hAD, hBD⟩ := pair_mem A hA B hB
          obtain ⟨U, hWU, g, hg, hb, rfl⟩ := hc hD
          exact Set.mem_sUnion.mpr
            ⟨_, hD, (LinearPMap.mk U g).graph.add_mem (hAD hx) (hBD hy)⟩
        smul_mem' := by
          intro a x hx
          obtain ⟨A, hA, hx⟩ := Set.mem_sUnion.mp hx
          obtain ⟨U, hWU, g, hg, hb, rfl⟩ := hc hA
          exact Set.mem_sUnion.mpr ⟨_, hA, (LinearPMap.mk U g).graph.smul_mem a hx⟩ }
    have hH : ∀ z ∈ H, z.1 = 0 → z.2 = 0 := by
      intro z hz hzero
      obtain ⟨A, hA, hz⟩ := Set.mem_sUnion.mp hz
      obtain ⟨U, hWU, g, hg, hb, rfl⟩ := hc hA
      exact (LinearPMap.mk U g).graph_fst_eq_zero_snd hz hzero
    let P := H.toLinearPMap
    have hgraph : P.graph = H := H.toLinearPMap_graph_eq hH
    have hbase : (LinearPMap.mk W f).graph ≤ P.graph := by
      rw [hgraph]
      obtain ⟨A, hA⟩ := hne
      obtain ⟨U, hWU, g, hg, hb, rfl⟩ := hc hA
      intro z hz
      exact Set.mem_sUnion.mpr ⟨_, hA, graph_mono hWU f g hg hz⟩
    have hle := LinearPMap.le_of_le_graph hbase
    refine ⟨⟨P.domain, hle.1, P.toFun, ?_, ?_, ?_⟩, ?_⟩
    · ext w
      exact (hle.2 (x := w) (y := Submodule.inclusion hle.1 w) rfl).symm
    · intro u
      have hu : ((u : V), P u) ∈ H := hgraph ▸ P.mem_graph u
      obtain ⟨A, hA, hu⟩ := Set.mem_sUnion.mp hu
      obtain ⟨U, hWU, g, hg, hb, rfl⟩ := hc hA
      obtain ⟨w, hw⟩ := (LinearPMap.mem_graph_iff' _).mp hu
      have hv := congrArg Prod.fst hw
      have hgval := congrArg Prod.snd hw
      change (w : V) = (u : V) at hv
      change g w = P u at hgval
      simpa only [LinearPMap.toFun_eq_coe, hv, hgval] using hb w
    · exact congrArg (fun T : Submodule K (V × K) ↦ (T : Set (V × K))) hgraph.symm
    · intro A hA z hz
      exact Set.mem_sUnion.mpr ⟨A, hA, hz⟩
  have maximal_exists : ∃ M : Set (V × K),
      Maximal (· ∈ boundedExtensionGraphs abv ν C W f) M := by
    apply zorn_subset
    intro c hc hchain
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨_, base_mem, by simp⟩
    · exact ⟨⋃₀ c, (chain_bound c hc hchain hne).1,
        (chain_bound c hc hchain hne).2⟩
  have full_domain : ∀ M : Set (V × K),
      Maximal (· ∈ boundedExtensionGraphs abv ν C W f) M →
      Prod.fst '' M = Set.univ := by
    intro M hM
    obtain ⟨U, hWU, g, hg, hb, rfl⟩ := hM.1
    have hU : ∀ x : V, x ∈ U := by
      intro x
      by_contra hx
      obtain ⟨G, hG, hGb⟩ := hext U hWU g hg hb x hx
      let T := U ⊔ Submodule.span K {x}
      have hWT : W ≤ T := hWU.trans le_sup_left
      have hGf : G.comp (Submodule.inclusion hWT) = f := by
        ext w
        have h1 := congrArg (fun k ↦ k (Submodule.inclusion hWU w)) hG
        have h2 := congrArg (fun k ↦ k w) hg
        exact h1.trans h2
      have hGM : ((LinearPMap.mk T G).graph : Set (V × K)) ∈
          boundedExtensionGraphs abv ν C W f := ⟨T, hWT, G, hGf, hGb, rfl⟩
      have hback := hM.2 hGM (graph_mono le_sup_left g G hG)
      have hxT : x ∈ T :=
        (show Submodule.span K {x} ≤ T from le_sup_right)
          (Submodule.mem_span_singleton_self x)
      exact hx (LinearPMap.mem_domain_of_mem_graph
        (hback ((LinearPMap.mk T G).mem_graph ⟨x, hxT⟩)))
    apply Set.eq_univ_of_forall
    intro x
    exact ⟨(x, g ⟨x, hU x⟩), (LinearPMap.mk U g).mem_graph ⟨x, hU x⟩, rfl⟩
  refine ⟨chain_bound, ⟨base_mem, by simp⟩, maximal_exists, full_domain, ?_⟩
  obtain ⟨M, hM⟩ := maximal_exists
  have hfull := full_domain M hM
  obtain ⟨U, hWU, g, hg, hb, rfl⟩ := hM.1
  have hU : ∀ x : V, x ∈ U := by
    intro x
    obtain ⟨z, hz, hzx⟩ := (hfull.symm ▸ Set.mem_univ x :
      x ∈ Prod.fst '' ((LinearPMap.mk U g).graph : Set (V × K)))
    exact hzx ▸ LinearPMap.mem_domain_of_mem_graph hz
  let lift : V →ₗ[K] U :=
    { toFun := fun x ↦ ⟨x, hU x⟩
      map_add' := fun _ _ ↦ Subtype.ext rfl
      map_smul' := fun _ _ ↦ Subtype.ext rfl }
  refine ⟨g.comp lift, ?_, ?_⟩
  · ext w
    exact congrArg (fun k ↦ k w) hg
  · intro v
    exact hb (lift v)

end LinearMap
