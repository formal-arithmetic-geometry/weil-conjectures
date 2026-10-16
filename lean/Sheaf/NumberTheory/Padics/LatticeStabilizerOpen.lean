/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.CompactOpen
public import Mathlib.LinearAlgebra.Basis.Defs
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.RingTheory.Nakayama
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Openness of a p-adic lattice stabilizer

Source: Stanford Weil II seminar, Lecture 19, Proposition 1.1.9, second bullet
(blueprint: lem-pod-lattice-stabilizer-open).
- The topology on the coefficient field is its spectral norm topology.
- The topology on the automorphisms is induced from compact-open continuous maps.
-/

@[expose] public section

universe u v

namespace Padic

private theorem spanning_isOpen {E M : Type*} [NormedField E] [AddCommGroup M]
    [Module E M] [FiniteDimensional E M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    (R : Subring E) (hR : ∀ x : E, ‖x‖ < 1 → x ∈ R)
    (b : Module.Basis (Fin (Module.finrank E M)) E M) (hb : Continuous b.equivFun)
    (Λ : Submodule R M) (hspan : Submodule.span E (Λ : Set M) = ⊤) :
    IsOpen (Λ : Set M) := by
  classical
  let c := Module.Basis.ofSpan hspan.ge
  let := FiniteDimensional.fintypeBasisIndex c
  have hc : Continuous c.equivFun := by
    have h := (c.equivFun.toLinearMap.comp b.equivFun.symm.toLinearMap).continuous_on_pi
    convert h.comp hb using 1
    ext x
    simp
  let U : Set M := ⋂ i, {x | ‖c.equivFun x i‖ < 1}
  have hU : IsOpen U := isOpen_iInter_of_finite fun i ↦
    isOpen_lt (((continuous_apply i).comp hc).norm) continuous_const
  have h0 : (0 : M) ∈ U := by simp [U]
  apply Λ.toAddSubgroup.isOpen_of_mem_nhds (g := 0)
  apply Filter.mem_of_superset (hU.mem_nhds h0)
  intro x hx
  rw [← c.sum_equivFun x]
  apply Λ.sum_mem
  intro i _
  have hi : c i ∈ Λ := Module.Basis.ofSpan_subset hspan.ge ⟨i, rfl⟩
  have hri : c.equivFun x i ∈ R := hR _ (Set.mem_iInter.mp hx i)
  exact Λ.smul_mem ⟨_, hri⟩ hi

private theorem image_eq_of_congr {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    (Λ : Submodule R M) (hFG : Λ.FG) (f g : M →ₗ[R] M)
    (hf : f '' (Λ : Set M) = (Λ : Set M))
    (hc : ∀ x ∈ Λ, g x - f x ∈ I • Λ) :
    g '' (Λ : Set M) = (Λ : Set M) := by
  have hgf : Λ.map g ≤ Λ := by
    rintro _ ⟨x, hx, rfl⟩
    have hfx : f x ∈ Λ := hf.le (Set.mem_image_of_mem f hx)
    simpa only [sub_add_cancel] using
      Λ.add_mem (Submodule.smul_le_right (hc x hx)) hfx
  apply Set.Subset.antisymm hgf
  have hle : Λ ≤ Λ.map g ⊔ I • Λ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hf.ge hy)
    have h1 : g x ∈ Λ.map g ⊔ I • Λ :=
      (show Λ.map g ≤ Λ.map g ⊔ I • Λ from le_sup_left) ⟨x, hx, rfl⟩
    have h2 : g x - f x ∈ Λ.map g ⊔ I • Λ :=
      (show I • Λ ≤ Λ.map g ⊔ I • Λ from le_sup_right) (hc x hx)
    simpa only [sub_sub_cancel] using (Λ.map g ⊔ I • Λ).sub_mem h1 h2
  exact Submodule.le_of_le_smul_of_le_jacobson_bot hFG hI hle

private theorem stabilizer_open_of_ideal {E M : Type*} [Field E] [AddCommGroup M]
    [Module E M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    (R : Subring E) (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    (Λ : Submodule R M) (hFG : Λ.FG) (hopen : IsOpen ((I • Λ : Submodule R M) : Set M)) :
    let : TopologicalSpace (M ≃L[E] M) :=
      TopologicalSpace.induced (fun g : M ≃L[E] M ↦ (g : C(M, M))) inferInstance
    IsOpen {g : M ≃L[E] M | g '' (Λ : Set M) = (Λ : Set M)} := by
  classical
  let : TopologicalSpace (M ≃L[E] M) :=
    TopologicalSpace.induced (fun g : M ≃L[E] M ↦ (g : C(M, M))) inferInstance
  obtain ⟨s, hs⟩ := hFG
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have heval (x : M) : Continuous (fun g : M ≃L[E] M ↦ g x) :=
    (continuous_eval_const x : Continuous (fun f : C(M, M) ↦ f x)).comp
      (continuous_induced_dom (f := fun g : M ≃L[E] M ↦ (g : C(M, M))))
  let U : Set (M ≃L[E] M) := ⋂ x ∈ s, {f | f x - g x ∈ I • Λ}
  have hU : IsOpen U := isOpen_biInter_finset fun x _ ↦
    hopen.preimage ((heval x).sub continuous_const)
  have hgU : g ∈ U := by simp [U]
  apply Filter.mem_of_superset (hU.mem_nhds hgU)
  intro f hf
  have hc : ∀ x ∈ Λ, f x - g x ∈ I • Λ := by
    have hle : Submodule.span R (s : Set M) ≤
        (I • Λ).comap ((f.toLinearMap - g.toLinearMap).restrictScalars R) := by
      apply Submodule.span_le.mpr
      intro x hx
      exact Set.mem_iInter₂.mp hf x hx
    rw [hs] at hle
    exact hle
  exact image_eq_of_congr I hI Λ ⟨s, hs⟩
    (g.toLinearMap.restrictScalars R) (f.toLinearMap.restrictScalars R) hg hc

/-- The stabilizer of a finitely generated spanning lattice is open.

Source: Stanford Weil II seminar, Lecture 19, Proposition 1.1.9, second bullet
(blueprint: lem-pod-lattice-stabilizer-open).

Proof: By `lem-sc-dvr-fg-torsionfree-free`, the lattice is free over the DVR supplied by
`def-weil-l-adic-coefficient-extension`. A lattice basis is an E-basis because the lattice
spans V. In that basis, preservation of the lattice is equivalent to both the matrix and
its inverse having entries in the valuation ring. For a stabilizing matrix A, every matrix
A+B with B in M_n(m_E) is invertible over the valuation ring: factor it as A(I+A⁻¹B), whose
second factor has determinant congruent to 1 modulo m_E, and use the adjugate formula.
Evaluation at a basis vector is continuous for the compact-open topology, and basis
coordinates are continuous for the specified product topology. Since m_E is the open
absolute-value ball of radius 1, the finitely many entry conditions defining A+M_n(m_E)
give an open neighborhood of A inside the stabilizer. Thus the stabilizer is open.

The coordinate hypothesis says that a basis coordinate equivalence is a homeomorphism onto
the finite product. All linear automorphisms are then continuous, so continuous linear
automorphisms represent the full GL_E(V). Their topology is explicitly induced from C(V,V),
whose Mathlib topology is compact-open, rather than from operator-norm continuous maps. -/
theorem lattice_stabilizer_isOpen (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    letI : NormedField E := spectralNorm.normedField ℚ_[l] E
    ∀ (V : Type v) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      [TopologicalSpace V],
      (∃ b : Module.Basis (Fin (Module.finrank E V)) E V,
        Continuous b.equivFun ∧ Continuous b.equivFun.symm) →
      ∀ (Λ : Submodule (coefficientExtensionIntegers l E) V),
        Λ.FG → Submodule.span E (Λ : Set V) = ⊤ →
        letI : TopologicalSpace (V ≃L[E] V) :=
          TopologicalSpace.induced (fun g : V ≃L[E] V ↦ (g : C(V, V))) inferInstance
        IsOpen {g : V ≃L[E] V | g '' (Λ : Set V) = (Λ : Set V)} := by
  classical
  let : NormedField E := spectralNorm.normedField ℚ_[l] E
  intro V _ _ _ _ hBasis Λ hFG hspan
  obtain ⟨b, hb, hb'⟩ := hBasis
  let e : V ≃ₜ (Fin (Module.finrank E V) → E) :=
    { b.equivFun.toEquiv with continuous_toFun := hb, continuous_invFun := hb' }
  have : IsTopologicalAddGroup V := e.isInducing.topologicalAddGroup b.equivFun.toAddEquiv
  have hdata := (extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  rcases hdata with ⟨hO, _, _, hlocal, hmax, _, _, _, _, hm0, _⟩
  have : IsLocalRing (coefficientExtensionIntegers l E) := hlocal
  have hI : coefficientExtensionMaximalIdeal l E ≤ Ideal.jacobson ⊥ := by
    have hm_eq : coefficientExtensionMaximalIdeal l E =
        IsLocalRing.maximalIdeal (coefficientExtensionIntegers l E) :=
      IsLocalRing.eq_maximalIdeal hmax
    rw [hm_eq]
    exact IsLocalRing.maximalIdeal_le_jacobson ⊥
  have hopen : IsOpen
      (((coefficientExtensionMaximalIdeal l E) • Λ :
        Submodule (coefficientExtensionIntegers l E) V) : Set V) := by
    refine spanning_isOpen (coefficientExtensionIntegers l E)
      (fun x hx ↦ (hO x).mpr hx.le) b hb _ ?_
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm0
    have haE : (a : E) ≠ 0 := by
      intro h
      apply ha0
      exact Subtype.ext h
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro x hx
    have hax : (a : E) • x ∈ Submodule.span E
        (((coefficientExtensionMaximalIdeal l E) • Λ :
          Submodule (coefficientExtensionIntegers l E) V) : Set V) :=
      Submodule.subset_span (Submodule.smul_mem_smul ha hx)
    have hinv := (Submodule.span E
        (((coefficientExtensionMaximalIdeal l E) • Λ :
          Submodule (coefficientExtensionIntegers l E) V) : Set V)).smul_mem
        (a : E)⁻¹ hax
    rw [smul_smul, inv_mul_cancel₀ haE, one_smul] at hinv
    exact hinv
  exact stabilizer_open_of_ideal (coefficientExtensionIntegers l E)
    (coefficientExtensionMaximalIdeal l E) hI Λ hFG hopen

end Padic
