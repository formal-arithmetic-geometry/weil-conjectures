/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
import WeilConjectures.SixFunctors.ProcyclicPrimary.ProcyclicPrimaryFactor
import WeilConjectures.SixFunctors.PadicPowersIndependent
import Mathlib.Topology.Constructions

/-!
# Free subgroups detected by a surjective adic character

Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-smooth-base-change/
sec-sbc-uniform/sk-rem-sbc-scope/sk-rem-sf-fullcd-scope.md`,
choice of the pro-r part of the closed procyclic subgroup.
(blueprint: lem-sf-padic-character-free-subgroup)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open Topology

/-- A character onto the additive adic integers has a continuous section in the closed
procyclic subgroup of any lift of one, and detects a countably generated free subgroup
there. Restrict the character to that procyclic subgroup, use its primary factor, then
transport the independent powers of an adic transcendental element through the section.
Source: the scope counterexample's choice of the subgroup H.
(blueprint: lem-sf-padic-character-free-subgroup) -/
theorem padicCharacterFreeSubgroup
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (r : ℕ) [Fact r.Prime] (χ : G →ₜ* Multiplicative ℤ_[r])
    (g : G) (hg : χ g = Multiplicative.ofAdd 1) :
    ∃ (j : Multiplicative ℤ_[r] →ₜ* G)
      (φ : Multiplicative (ULift.{w} ℕ →₀ ℤ) →* G),
      (∀ z, j z ∈ (Subgroup.zpowers g).topologicalClosure) ∧
      (∀ z, χ (j z) = z) ∧ (∀ h, φ h ∈ Set.range j) ∧
      Function.Injective (χ.toMonoidHom.comp φ) := by
  classical
  let C := (Subgroup.zpowers g).topologicalClosure
  have : CompactSpace C :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_topologicalClosure _).isCompact
  let gC : C := ⟨g, Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers g)⟩
  have hd : DenseRange (fun n : ℤ ↦ gC ^ n) := by
    rw [DenseRange, Subtype.dense_iff]
    intro x hx
    change x ∈ closure ((Subtype.val : C → G) '' Set.range (fun n : ℤ ↦ gC ^ n))
    rw [← Set.range_comp]
    change x ∈ closure (Set.range (fun n : ℤ ↦ g ^ n))
    simpa only [C, Subgroup.topologicalClosure_coe, Subgroup.coe_zpowers] using hx
  let χC : C →ₜ* Multiplicative ℤ_[r] :=
    ⟨χ.toMonoidHom.comp C.subtype, χ.continuous.comp continuous_subtype_val⟩
  obtain ⟨q, _, _, _, _, _, ⟨e, he⟩, _, _⟩ :=
    ProcyclicPrimary.procyclic_primary_factor C gC hd r χC hg
  let j : Multiplicative ℤ_[r] →ₜ* G :=
    ⟨C.subtype.comp ((ProcyclicPrimary.primaryImage q.toMonoidHom r).subtype.comp
      e.symm.toMulEquiv.toMonoidHom),
      continuous_subtype_val.comp (continuous_subtype_val.comp e.symm.continuous)⟩
  have hj (z : Multiplicative ℤ_[r]) : χ (j z) = z := by
    change χC (e.symm z : C) = z
    rw [← he, e.apply_symm_apply]
  obtain ⟨t, ht, _⟩ := exists_padic_powers_independent r
  let a : (ULift.{w} ℕ →₀ ℤ) →+ ℤ_[r] :=
    (Finsupp.linearCombination ℤ (fun n : ULift.{w} ℕ ↦ t ^ n.down)).toAddMonoidHom
  have ha : Function.Injective a :=
    (ht.comp _ ULift.down_injective).finsuppLinearCombination_injective
  let φ := j.toMonoidHom.comp a.toMultiplicative
  refine ⟨j, φ, fun z ↦ (e.symm z : C).property, hj, fun h ↦ ⟨_, rfl⟩, ?_⟩
  intro x y hxy
  apply ha
  change a x.toAdd = a y.toAdd
  change χ (j (a.toMultiplicative x)) = χ (j (a.toMultiplicative y)) at hxy
  rw [hj, hj] at hxy
  exact congrArg Multiplicative.toAdd hxy
