/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker E6
-/
module

public import Sheaf.RepresentationTheory.ProcyclicComplex
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Sheaf.RepresentationTheory.CoinducedDiscreteEmbedding
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Fixed vectors for the additive generator of the l-adic integers

Source: blueprint lem-exc-procyclic-two-term, first proof paragraph.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace Rep

set_option linter.style.haveILetI false in
/-- A vector fixed by the additive generator is invariant under all l-adic integers.

Proof: the orbit map is locally constant by the coinduced embedding. It is constant
on nonnegative integer multiples of the generator by induction. Those multiples are
dense in the l-adic integers, so continuity makes the orbit map constant everywhere.
Source: blueprint lem-exc-procyclic-two-term, first paragraph
(blueprint: lem-exc-procyclic-homology-zero). -/
private theorem procyclic_fixed_iff (l : ℕ) [Fact l.Prime] (A : Type u) [Ring A] [Finite A]
    (M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l])) (m : M.obj.V) :
    M.obj.ρ (Multiplicative.ofAdd (1 : ℤ_[l])) m = m ↔
      ∀ g : Multiplicative ℤ_[l], M.obj.ρ g m = m := by
  constructor
  · intro hm
    obtain ⟨D, e, ι, _, _, hι, _⟩ :=
      exists_coinduced_discrete_embedding.{0, u, w} (Multiplicative ℤ_[l]) A
    let f : LocallyConstant (Multiplicative ℤ_[l]) M.obj.V :=
      e M ((ι.app M).hom.hom m)
    have hf (g : Multiplicative ℤ_[l]) : f g = M.obj.ρ g m := hι M m g
    have hn (n : ℕ) : M.obj.ρ (Multiplicative.ofAdd (n : ℤ_[l])) m = m := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Nat.cast_add, Nat.cast_one]
        change M.obj.ρ (Multiplicative.ofAdd (n : ℤ_[l]) *
          Multiplicative.ofAdd (1 : ℤ_[l])) m = m
        rw [map_mul]
        change M.obj.ρ (Multiplicative.ofAdd (n : ℤ_[l]))
          (M.obj.ρ (Multiplicative.ofAdd (1 : ℤ_[l])) m) = m
        rw [hm, ih]
    letI : TopologicalSpace M.obj.V := ⊥
    letI : DiscreteTopology M.obj.V := ⟨rfl⟩
    have heq : (fun x : ℤ_[l] ↦ f (Multiplicative.ofAdd x)) = fun _ ↦ m := by
      apply PadicInt.denseRange_natCast.equalizer f.continuous continuous_const
      funext n
      exact (hf _).trans (hn n)
    intro g
    exact (hf g).symm.trans (congrFun heq (Multiplicative.toAdd g))
  · intro h
    exact h _

/-- Zeroth two-term homology is any naturally realized invariant functor.

Proof: the invariant inclusion is the kernel of the differential by
`procyclic_fixed_iff`. The universal property of the kernel identifies it with cycles.
No boundaries enter degree zero, so cycles are homology. Equivariant coefficient maps
commute with both inclusions, proving naturality by cancellation of a monomorphism.
Source: blueprint lem-exc-procyclic-two-term, first proof paragraph
(blueprint: lem-exc-procyclic-homology-zero). -/
theorem actionTwoTerm_homology_zero
    (l : ℕ) [Fact l.Prime] (A : Type u) [Ring A] [Finite A]
    (V : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]) ⥤ ModuleCat.{w} A)
    (t : ∀ M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]),
      V.obj M ≃ₗ[A] (⨅ g, LinearMap.ker (M.obj.ρ g - LinearMap.id) :
        Submodule A M.obj.V))
    (ht : ∀ (M N : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]))
      (f : M ⟶ N) (x : V.obj M),
      (t N ((V.map f).hom x)).val = f.hom.hom (t M x).val) :
    Nonempty ((actionTwoTerm A (Multiplicative ℤ_[l])
      (Multiplicative.ofAdd (1 : ℤ_[l])) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{w} A) (ComplexShape.up ℕ) 0) ≅ V) := by
  classical
  let K := actionTwoTerm.{u, 0, w} A (Multiplicative ℤ_[l])
    (Multiplicative.ofAdd (1 : ℤ_[l]))
  let i (M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l])) :
      V.obj M ⟶ (K.obj M).X 0 :=
    ModuleCat.ofHom ((⨅ g, LinearMap.ker (M.obj.ρ g - LinearMap.id)).subtype.comp
      (t M).toLinearMap)
  have hi (M) : Function.Injective (i M).hom :=
    Subtype.val_injective.comp (t M).injective
  have hex (M) : Function.Exact (i M).hom ((K.obj M).d 0 1).hom := by
    intro x
    change M.obj.V at x
    change M.obj.ρ (Multiplicative.ofAdd (1 : ℤ_[l])) x - x = 0 ↔ _
    rw [sub_eq_zero, procyclic_fixed_iff]
    constructor
    · intro hx
      have hx' : x ∈ ⨅ g, LinearMap.ker (M.obj.ρ g - LinearMap.id) := by
        simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.id_apply, sub_eq_zero]
        exact hx
      exact ⟨(t M).symm ⟨x, hx'⟩, congrArg Subtype.val ((t M).apply_symm_apply _)⟩
    · rintro ⟨y, rfl⟩ g
      have h := (t M y).property
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at h
      exact h g
  let hv (M) := ModuleCat.isLimitKernelFork (i M) ((K.obj M).d 0 1) (hex M) (hi M)
  let e (M) : (K.obj M).cycles 0 ≅ V.obj M :=
    (K.obj M).cyclesIsKernel 0 (j := 1) (by simp) |>.conePointUniqueUpToIso (hv M)
  have he (M) : (e M).hom ≫ i M = (K.obj M).iCycles 0 := by
    exact IsLimit.conePointUniqueUpToIso_hom_comp
      ((K.obj M).cyclesIsKernel 0 (j := 1) (by simp)) (hv M) WalkingParallelPair.zero
  let ez (M) : (K.obj M).homology 0 ≅ V.obj M :=
    (K.obj M).isoHomologyπ₀.symm ≪≫ e M
  have hez (M) : (ez M).hom ≫ i M =
      (K.obj M).isoHomologyπ₀.inv ≫ (K.obj M).iCycles 0 := by
    simp only [ez, Iso.trans_hom, Iso.symm_hom, Category.assoc, he]
  refine ⟨NatIso.ofComponents ez ?_⟩
  intro M N f
  have : Mono (i N) := (ModuleCat.mono_iff_injective _).mpr (hi N)
  apply (cancel_mono (i N)).mp
  simp only [Category.assoc, hez]
  change HomologicalComplex.homologyMap (K.map f) 0 ≫
      (K.obj N).isoHomologyπ₀.inv ≫ (K.obj N).iCycles 0 = _
  rw [← Category.assoc, CochainComplex.isoHomologyπ₀_inv_naturality]
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
  rw [← Category.assoc, ← hez]
  simp only [Category.assoc]
  congr 1
  ext x
  exact (ht M N f x).symm

end Rep
