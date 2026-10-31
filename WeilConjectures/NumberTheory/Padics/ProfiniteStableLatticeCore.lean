/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Topology.Algebra.Group.Basic
import WeilConjectures.NumberTheory.Padics.LatticeStabilizerOpen
import Mathlib.Algebra.Module.Lattice
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

universe u v w

namespace Padic

/-- The algebraic part of the compact-group stable-lattice construction.

Source: Stanford Weil II seminar, lecture 19, Proposition 1.1.9, pp. 2–3.
(blueprint: lem-pod-profinite-stable-lattice-core).
The proof chooses a basis, uses the open lattice stabilizer, takes finitely many coset
translates, and applies the DVR finite torsion-free freeness theorem. -/
 theorem exists_stable_lattice_core (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (V : Type w) [AddCommGroup V] [Module E V] [FiniteDimensional E V] :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    letI : TopologicalSpace V := moduleTopology E V
    let O := coefficientExtensionIntegers l E
    letI : Module O V := Module.compHom V O.subtype
    ∀ (ρ : G →* (V ≃ₗ[E] V)), Continuous (fun p : G × V ↦ ρ p.1 p.2) →
      ∃ Λ : Submodule O V,
        Λ.FG ∧ Submodule.span E (Λ : Set V) = ⊤ ∧
        Module.Free O Λ ∧ Module.finrank O Λ = Module.finrank E V ∧
        (∀ g : G, (ρ g) '' (Λ : Set V) = (Λ : Set V)) := by
  classical
  dsimp
  intro ρ hρ
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let : TopologicalSpace V := moduleTopology E V
  let O := coefficientExtensionIntegers l E
  let : Module O V := Module.compHom V O.subtype
  let : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup E V
  let b := Module.finBasis E V
  have hb : Continuous b.equivFun := by
    exact IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  let Λ₀ : Submodule O V := Submodule.span O (Set.range b)
  have hfg : Λ₀.FG := Submodule.fg_span (Set.toFinite _)
  have hspan : Submodule.span E (Λ₀ : Set V) = ⊤ := by
    change Submodule.span E ((Submodule.span O (Set.range b) : Submodule O V) : Set V) = ⊤
    rw [Submodule.span_span_of_tower O E]
    exact b.span_eq
  let F : G → (V ≃L[E] V) := fun g ↦
    { toLinearEquiv := ρ g
      continuous_toFun := hρ.comp (continuous_const.prodMk continuous_id)
      continuous_invFun :=
        IsModuleTopology.continuous_of_linearMap (ρ g).symm.toLinearMap }
  let : TopologicalSpace (V ≃L[E] V) :=
    TopologicalSpace.induced (fun g : V ≃L[E] V ↦ (g : C(V, V))) inferInstance
  have hFC : Continuous (fun g : G ↦ (F g : C(V, V))) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : G × V ↦ ρ p.1 p.2)
    exact hρ
  have hF : Continuous F := by
    exact continuous_induced_rng.mpr hFC
  have hopen := lattice_stabilizer_isOpen l E V ⟨b, hb, by
    exact IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap⟩ Λ₀ hfg hspan
  let H : Subgroup G :=
    { carrier := {g | (ρ g) '' (Λ₀ : Set V) = (Λ₀ : Set V)}
      one_mem' := by simp
      mul_mem' := by
        intro g h hg hh
        change (ρ (g * h)) '' (Λ₀ : Set V) = _
        rw [map_mul]
        change ((ρ g) ∘ (ρ h)) '' (Λ₀ : Set V) = _
        rw [Set.image_comp, hh, hg]
      inv_mem' := by
        intro g hg
        change (ρ g) '' (Λ₀ : Set V) = _ at hg
        change (ρ g⁻¹) '' (Λ₀ : Set V) = _
        apply Set.Subset.antisymm
        · rintro y ⟨x, hx, rfl⟩
          obtain ⟨z, hz, hzx⟩ := hg.ge hx
          simpa [← hzx] using hz
        · intro y hy
          refine ⟨ρ g y, hg.le ⟨y, hy, rfl⟩, ?_⟩
          simp }
  have hH : IsOpen (H : Set G) := hopen.preimage hF
  have : Finite (G ⧸ H) := H.quotient_finite_of_isOpen hH
  let L : Submodule O V := Submodule.span O
    (Set.range fun p : G × Fin (Module.finrank E V) ↦ ρ p.1 (b p.2))
  have hbL (i) : b i ∈ L := Submodule.subset_span ⟨(1, i), by simp⟩
  let T : G ⧸ H → Submodule O V := fun q ↦
    Λ₀.map ((ρ q.out).restrictScalars O).toLinearMap
  have hLT : L ≤ ⨆ q, T q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, i⟩, rfl⟩
    let q : G ⧸ H := QuotientGroup.mk g
    have hh : q.out⁻¹ * g ∈ H := QuotientGroup.eq.mp (QuotientGroup.out_eq' q)
    have hmem : ρ (q.out⁻¹ * g) (b i) ∈ Λ₀ :=
      (show (ρ (q.out⁻¹ * g)) '' (Λ₀ : Set V) = _ from hh).le
        ⟨b i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
    apply (le_iSup T q)
    refine ⟨ρ (q.out⁻¹ * g) (b i), hmem, ?_⟩
    change ρ q.out (ρ (q.out⁻¹ * g) (b i)) = ρ g (b i)
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel_left]
  have hTL : (⨆ q, T q) ≤ L := by
    apply iSup_le
    intro q
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨(q.out, i), rfl⟩
  have hLfg : L.FG := by
    rw [le_antisymm hLT hTL]
    exact Submodule.fg_iSup T (fun q ↦ hfg.map _)
  have hLspan : Submodule.span E (L : Set V) = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    exact Submodule.span_mono (Set.range_subset_iff.mpr hbL)
  have hstab (g : G) : ∀ x ∈ L, ρ g x ∈ L := by
    have hle : L ≤ L.comap ((ρ g).restrictScalars O).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨h, i⟩, rfl⟩
      change ρ g (ρ h (b i)) ∈ L
      rw [← LinearEquiv.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨(g * h, i), rfl⟩
    exact hle
  have hstable (g : G) : (ρ g) '' (L : Set V) = (L : Set V) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hstab g x hx
    · intro x hx
      refine ⟨ρ g⁻¹ x, hstab g⁻¹ x hx, ?_⟩
      rw [map_inv]
      exact (ρ g).apply_symm_apply x
  have hdvr := (extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  let : Algebra O E := RingHom.toAlgebra O.subtype
  let : IsScalarTower O E V := ⟨fun a x v ↦ by
    change ((a : E) * x) • v = (a : E) • (x • v)
    exact mul_smul (a : E) x v⟩
  have : IsFractionRing O E := hdvr.2.2.2.2.2.2.1
  have : IsPrincipalIdealRing O := hdvr.2.2.2.2.2.2.2.2.1
  have : Submodule.IsLattice E L := ⟨hLfg, hLspan⟩
  refine ⟨L, hLfg, hLspan, inferInstance, ?_, hstable⟩
  apply Module.finrank_eq_of_rank_eq
  rw [Submodule.IsLattice.rank' E L, Module.finrank_eq_rank]

end Padic
