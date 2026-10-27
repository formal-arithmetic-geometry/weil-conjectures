/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
import Sheaf.NumberTheory.Padics.CountableClosedFiniteCover
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Compactness.Compact

/-! # Finite-field values on an open coset rectangle

Source: agent arithmetic expansion of paragraph (3) of the current blueprint's
`sk-thm-sf-ctf-stability-direct-images.proof.md`; Stanford Weil II seminar, L19,
Proposition 1.1.9, p. 3; Stacks Project, Tag 0CQN
(blueprint: lem-sfb-profinite-map-finite-field-rectangle).

The algebraic closure has the extended norm topology. The group is compact Hausdorff
and has an open-subgroup identity neighbourhood basis. No normality is required.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open Topology

namespace Padic

/-- A continuous map from a positive finite power of a profinite group to a finite power
of a p-adic algebraic closure takes values in one finite intermediate field on a common
open-subgroup coset rectangle. The multiplication order is `h i * a i`.

Source: agent arithmetic expansion of paragraph (3) of the current blueprint's
`sk-thm-sf-ctf-stability-direct-images.proof.md`; Stanford Weil II seminar, L19,
Proposition 1.1.9, p. 3; Stacks Project, Tag 0CQN
(blueprint: lem-sfb-profinite-map-finite-field-rectangle).

Proof:
1. Apply lem-sfb-algcl-countable-closed-finite-cover to obtain increasing closed finite
   intermediate fields F_j containing E and covering the algebraic closure. In G^m let
   A_j be the set where all d coordinates of f lie in F_j. These sets are closed by
   coordinate continuity and finite intersection. They cover G^m: for each tuple take
   the maximum of the finitely many indices needed for its coordinates. For d = 0,
   A_0 is the whole product, so the same cover conclusion holds.
2. By lem-weil-pbc-tychonoff-product-quasi-compact the product G^m is compact. It is
   Hausdorff, nonempty (the identity tuple), and locally compact. Apply
   lem-sfb-baire-closed-cover-interior to this full subspace and the closed cover A_j.
   Some A_j has nonempty interior; choose a tuple a in that interior.
3. Choose a basic open box with coordinate neighbourhoods U_i of a_i inside A_j.
   Right translation by a_i inverse carries U_i to an identity neighbourhood. Choose
   an open subgroup H_i inside that neighbourhood by hG. Their finite intersection H
   is open, and h_i * a_i lies in U_i whenever h_i lies in H. Consequently the whole
   rectangle maps into F_j^d. Take F = F_j, with H and the chosen centres a.
-/
theorem exists_finiteIntermediateField_coset_rectangle
    (ℓ : ℕ) [Fact ℓ.Prime] (Ω : Type u) [NormedField Ω]
    [NormedAlgebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]
    (E : IntermediateField (Padic ℓ) Ω) [FiniteDimensional (Padic ℓ) E]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    (hG : ∀ U ∈ nhds (1 : G), ∃ H : OpenSubgroup G, (H : Set G) ⊆ U)
    (m : ℕ) (hm : 1 ≤ m) (d : ℕ)
    (f : (Fin m → G) → (Fin d → Ω)) (hf : Continuous f) :
    ∃ F : IntermediateField (Padic ℓ) Ω,
      E ≤ F ∧ FiniteDimensional (Padic ℓ) F ∧
      ∃ (H : OpenSubgroup G) (a : Fin m → G),
        ∀ h : Fin m → H, ∀ r : Fin d, f (fun i ↦ (h i : G) * a i) r ∈ F := by
  classical
  have _ := hm
  obtain ⟨F, hmono, hF, hcover⟩ :=
    exists_monotone_closed_finiteIntermediateField_cover ℓ Ω E
  let A (j : ℕ) : Set (Fin m → G) := {x | ∀ r, f x r ∈ F j}
  have hclosed (j : ℕ) : IsClosed (A j) := by
    dsimp only [A]
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun r ↦
      (hF j).2.2.preimage ((continuous_apply r).comp hf)
  have hAcover : (⋃ j, A j) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx (r : Fin d) : ∃ j, f x r ∈ F j := by
      have : f x r ∈ ⋃ j, (F j : Set Ω) := by rw [hcover]; trivial
      exact Set.mem_iUnion.mp this
    choose n hn using hx
    refine Set.mem_iUnion.mpr ⟨Finset.univ.sup n, ?_⟩
    intro r
    exact hmono (Finset.le_sup (Finset.mem_univ r)) (hn r)
  obtain ⟨j, a, ha⟩ := nonempty_interior_of_iUnion_of_closed hclosed hAcover
  let t : (Fin m → G) → (Fin m → G) := fun h i ↦ h i * a i
  have ht : Continuous t := continuous_pi fun i ↦ (continuous_apply i).mul continuous_const
  have hpre : t ⁻¹' A j ∈ nhds (fun _ : Fin m ↦ (1 : G)) := by
    have hat : t (fun _ ↦ 1) = a := by ext i; exact one_mul _
    apply ht.continuousAt.preimage_mem_nhds
    rw [hat]
    exact mem_interior_iff_mem_nhds.mp ha
  rw [nhds_pi] at hpre
  obtain ⟨I, U, hU, hsub⟩ := Filter.mem_pi'.mp hpre
  choose K hK using fun i ↦ hG (U i) (hU i)
  let H : OpenSubgroup G := Finset.univ.inf K
  refine ⟨F j, (hF j).1, (hF j).2.1, H, a, ?_⟩
  intro h r
  apply hsub (show (fun i ↦ (h i : G)) ∈ (I : Set (Fin m)).pi U from ?_) r
  intro i _
  exact hK i ((Finset.inf_le (Finset.mem_univ i) : H ≤ K i) (h i).property)

end Padic
