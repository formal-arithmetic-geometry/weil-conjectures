/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
import Sheaf.Topology.SpectralLimitDescendOpens

/-! # Simultaneous descent of finite compact-open covers

Source: Stacks Project, Sheaves, Tag 0A32, surjectivity paragraph;
Topology, Tag 0A30.
(blueprint: lem-weil-pbc-spectral-limit-descend-finite-cover)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open TopologicalSpace

namespace Topology

/-- A finite compact-open cover of a limit open descends, with its prescribed
inclusions into opens at the original stage.

Proof: Descend each covering open by 0A30(1), and choose a common upper bound of
these finitely many stages and i. Pulling their representatives to this bound gives
compact opens with the original pullbacks. Descend the covering equality by 0A30(3).
Descend each prescribed inclusion by 0A30(2), choose a common upper bound of these
finitely many stages, and pull everything to that bound. Inverse images preserve
covering equalities, inclusions and compactness under the spectral transitions.
For the empty family, the same argument descends emptiness of the covered open.
Source: Stacks Project, Sheaves, Tag 0A32, surjectivity paragraph; Topology, Tag 0A30.
(blueprint: lem-weil-pbc-spectral-limit-descend-finite-cover) -/
theorem spectralLimit_descend_finite_cover
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : I → Type u) [∀ i : I, TopologicalSpace (S i)] [∀ i : I, SpectralSpace (S i)]
    (f : ∀ (i j : I), i ≤ j → S j → S i)
    (hf : ∀ (i j : I) (h : i ≤ j), IsSpectralMap (f i j h))
    (hfid : ∀ (i : I) (x : S i), f i i le_rfl x = x)
    (hfcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (x : S k),
      f i j hij (f j k hjk x) = f i k (hij.trans hjk) x)
    (X : Type v) [TopologicalSpace X] (p : ∀ i : I, X → S i)
    (hp : ∀ i : I, Continuous (p i))
    (hpcomp : ∀ (i j : I) (h : i ≤ j) (x : X), f i j h (p j x) = p i x)
    (hlimit : ∀ a : ∀ i : I, S i,
      (∀ (i j : I) (h : i ≤ j), f i j h (a j) = a i) →
      ∃! x : X, ∀ i : I, p i x = a i)
    (htop : ‹TopologicalSpace X› =
      ⨅ i : I, TopologicalSpace.induced (p i) inferInstance)
    (i : I) (U : Set (S i)) (hUo : IsOpen U) (hUc : IsCompact U)
    (n : ℕ) (V : Fin n → Set (S i)) (W : Fin n → Set X)
    (hV : ∀ a, IsOpen (V a) ∧ IsCompact (V a))
    (hW : ∀ a, IsOpen (W a) ∧ IsCompact (W a))
    (hcover : p i ⁻¹' U = ⋃ a, W a)
    (hincl : ∀ a, W a ⊆ p i ⁻¹' V a) :
    ∃ (j : I) (hij : i ≤ j) (D : Fin n → Set (S j)),
      (∀ a, IsOpen (D a) ∧ IsCompact (D a)) ∧
      f i j hij ⁻¹' U = ⋃ a, D a ∧
      (∀ a, p j ⁻¹' D a = W a) ∧
      (∀ a, D a ⊆ f i j hij ⁻¹' V a) := by
  classical
  have hd := spectralLimit_descend_opens S f hf hfid hfcomp X p hp hpcomp hlimit htop
  have hpre (a b c : I) (hab : a ≤ b) (hbc : b ≤ c) (T : Set (S a)) :
      f b c hbc ⁻¹' (f a b hab ⁻¹' T) = f a c (hab.trans hbc) ⁻¹' T := by
    ext x
    simp only [Set.mem_preimage, hfcomp]
  have hppre (a b : I) (hab : a ≤ b) (T : Set (S a)) :
      p b ⁻¹' (f a b hab ⁻¹' T) = p a ⁻¹' T := by
    ext x
    simp only [Set.mem_preimage, hpcomp]
  choose a A hAo hAc hA using fun t ↦ hd.1 (W t) (hW t).1 (hW t).2
  obtain ⟨k, hk⟩ := ((Set.finite_range a).insert i).bddAbove
  have hik : i ≤ k := hk (by simp)
  have hak (t : Fin n) : a t ≤ k := hk (Set.mem_insert_of_mem _ (Set.mem_range_self t))
  let E (t : Fin n) := f (a t) k (hak t) ⁻¹' A t
  have hE (t : Fin n) : IsOpen (E t) ∧ IsCompact (E t) :=
    ⟨(hAo t).preimage (hf _ _ _).continuous,
      (hf _ _ _).isCompact_preimage_of_isOpen (hAo t) (hAc t)⟩
  have hpE (t : Fin n) : p k ⁻¹' E t = W t := (hppre _ _ _ _).trans (hA t)
  have hcov : p k ⁻¹' (f i k hik ⁻¹' U) = ⋃ t, p k ⁻¹' E t := by
    rw [hppre, hcover]
    exact Set.iUnion_congr fun t ↦ (hpE t).symm
  obtain ⟨q, hkq, hq⟩ := hd.2.2.1 k n (f i k hik ⁻¹' U) E
    (hUo.preimage (hf _ _ _).continuous)
    ((hf _ _ _).isCompact_preimage_of_isOpen hUo hUc) hE hcov
  let Q (t : Fin n) := f k q hkq ⁻¹' E t
  have hQ (t : Fin n) : IsOpen (Q t) ∧ IsCompact (Q t) :=
    ⟨(hE t).1.preimage (hf _ _ _).continuous,
      (hf _ _ _).isCompact_preimage_of_isOpen (hE t).1 (hE t).2⟩
  have hpQ (t : Fin n) : p q ⁻¹' Q t = W t := (hppre _ _ _ _).trans (hpE t)
  have hqcover : f i q (hik.trans hkq) ⁻¹' U = ⋃ t, Q t := by
    rw [← hpre i k q hik hkq U]
    exact hq
  choose l hql hil hl using fun t ↦ hd.2.1 q i (Q t) (V t)
    (hQ t).1 (hQ t).2 (hV t).1 (hV t).2 (by rw [hpQ]; exact hincl t)
  obtain ⟨m, hm⟩ := ((Set.finite_range l).insert q).bddAbove
  have hqm : q ≤ m := hm (by simp)
  have hlm (t : Fin n) : l t ≤ m := hm (Set.mem_insert_of_mem _ (Set.mem_range_self t))
  let D (t : Fin n) := f q m hqm ⁻¹' Q t
  refine ⟨m, (hik.trans hkq).trans hqm, D, ?_, ?_, ?_, ?_⟩
  · intro t
    exact ⟨(hQ t).1.preimage (hf _ _ _).continuous,
      (hf _ _ _).isCompact_preimage_of_isOpen (hQ t).1 (hQ t).2⟩
  · rw [← hpre i q m (hik.trans hkq) hqm U, hqcover, Set.preimage_iUnion]
  · intro t
    exact (hppre _ _ _ _).trans (hpQ t)
  · intro t x hx
    change f q m hqm x ∈ Q t at hx
    have hx' : f (l t) m (hlm t) x ∈ f q (l t) (hql t) ⁻¹' Q t := by
      simpa only [Set.mem_preimage, hfcomp] using hx
    have h := hl t hx'
    simpa only [Set.mem_preimage, hfcomp] using h

end Topology
