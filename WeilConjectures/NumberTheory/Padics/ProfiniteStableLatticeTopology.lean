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

import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace

@[expose] public section

universe u v w

namespace Padic


open scoped Topology

private theorem adicLinearMapContinuous {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (f : M →ₗ[R] N) :
    @Continuous M N (I.adicModuleTopology M) (I.adicModuleTopology N) f := by
  let : TopologicalSpace M := I.adicModuleTopology M
  let : TopologicalSpace N := I.adicModuleTopology N
  apply continuous_of_tendsto_nhds_zero f
  let : TopologicalSpace R := I.adicTopology
  let BM := (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)).toAddGroupFilterBasis
  let BN := (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis N)).toAddGroupFilterBasis
  rw [BM.nhds_zero_hasBasis.tendsto_iff BN.nhds_zero_hasBasis]
  rintro U ⟨n, rfl⟩
  refine ⟨(I ^ n • ⊤ : Submodule R M), ⟨n, rfl⟩, ?_⟩
  intro x hx
  exact Submodule.smul_top_le_comap_smul_top (I ^ n) f hx

private theorem adicFreeModuleTopology {R M : Type*} [CommRing R] [StrongRankCondition R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (I : Ideal R) :
    letI : TopologicalSpace R := I.adicTopology
    letI : TopologicalSpace M := I.adicModuleTopology M
    IsModuleTopology R M := by
  classical
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace M := I.adicModuleTopology M
  let : IsTopologicalRing R := I.ringFilterBasis.isTopologicalRing
  let B := I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)
  let : IsTopologicalAddGroup M := B.toAddGroupFilterBasis.isTopologicalAddGroup
  let : ContinuousSMul R M := B.continuousSMul
  let b := Module.finBasis R M
  have hc : Continuous b.equivFun := by
    apply continuous_pi
    intro i
    exact adicLinearMapContinuous I (b.coord i)
  have hi : Continuous b.equivFun.symm := by
    rw [show b.equivFun.symm = (fun x : Fin (Module.finrank R M) → R ↦
      ∑ i, x i • b i) by
      funext x
      exact Module.Basis.equivFun_symm_apply b x]
    exact continuous_finsetSum Finset.univ
      (fun i _ ↦ (continuous_apply i).smul continuous_const)
  let e : M ≃L[R] (Fin (Module.finrank R M) → R) :=
    { b.equivFun with continuous_toFun := hc, continuous_invFun := hi }
  exact IsModuleTopology.iso e.symm

private theorem coefficientAdicTopology (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    (coefficientExtensionMaximalIdeal l E).adicTopology =
      TopologicalSpace.induced (fun x : coefficientExtensionIntegers l E ↦ (x : E))
        inferInstance := by
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let O := coefficientExtensionIntegers l E
  let I := coefficientExtensionMaximalIdeal l E
  have hdvr := (extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span ({coefficientExtensionUniformizer l E} : Set O) = I :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hideal (n : ℕ) : coefficientExtensionIdeal l E n = I ^ n := by
    change Ideal.span ({coefficientExtensionUniformizer l E} : Set O) ^ n = I ^ n
    rw [hgen]
  apply TopologicalSpace.ext_nhds
  intro x
  apply (I.hasBasis_nhds_adic x).ext (coefficientExtension_integers_coset_basis l E x)
  · intro n _
    refine ⟨n, trivial, ?_⟩
    intro y hy
    have hmem : y - x ∈ I ^ (n + 1) := by
      simpa only [Set.mem_ofPred_eq, Ideal.Quotient.eq, hideal] using hy
    exact ⟨y - x, Ideal.pow_le_pow_right (Nat.le_succ n) hmem, by simp⟩
  · intro n _
    refine ⟨n + 1, trivial, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    change Ideal.Quotient.mk (coefficientExtensionIdeal l E (n + 1)) (x + z) = _
    rw [Ideal.Quotient.eq, hideal, add_sub_cancel_left]
    exact hz


/-- The adic topology on a finitely generated full free lattice is the subspace topology.

Source: Stanford Weil II seminar, lecture 19, Proposition 1.1.9, p. 3.
(blueprint: lem-pod-profinite-stable-lattice-topology).

Proof: the coefficient-ring coset basis identifies its adic and spectral subspace topologies.
The ring is compact because it is the closed unit ball in the proper field E. Integral basis
coordinates give the lattice its module topology, so finite generation makes it compact.
Its inclusion into V is linear and continuous; field coordinates make V Hausdorff. A continuous
injection from a compact space into a Hausdorff space is an embedding, giving the equality. -/
private theorem stable_lattice_adic_topology_eq_induced
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (V : Type w) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (Λ : Submodule (coefficientExtensionIntegers l E) V)
    (hfg : Λ.FG) (hfree : Module.Free (coefficientExtensionIntegers l E) Λ) :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    letI : TopologicalSpace V := moduleTopology E V
    letI : Module (coefficientExtensionIntegers l E) V :=
      Module.compHom V (coefficientExtensionIntegers l E).subtype
    (coefficientExtensionMaximalIdeal l E).adicModuleTopology Λ =
      TopologicalSpace.induced (fun x : Λ ↦ (x : V)) inferInstance := by
  classical
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let : NormedSpace ℚ_[l] E := spectralNorm.normedSpace ℚ_[l] E
  let : ProperSpace E := FiniteDimensional.proper ℚ_[l] E
  let : TopologicalSpace V := moduleTopology E V
  let : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup E V
  let O := coefficientExtensionIntegers l E
  let I := coefficientExtensionMaximalIdeal l E
  let : Module O V := Module.compHom V O.subtype
  let : Module.Free O Λ := hfree
  let : Module.Finite O Λ := Module.Finite.of_fg hfg
  have hdvr := (extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hO : ∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1 := hdvr.1
  have hcompact : @CompactSpace O (TopologicalSpace.induced (fun x : O ↦ (x : E))
      inferInstance) := by
    rw [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ,
      Subtype.range_coe_subtype]
    change IsCompact (O : Set E)
    have hball : (O : Set E) = Metric.closedBall 0 1 := by
      ext x
      rw [SetLike.mem_coe, hO]
      simp only [Metric.mem_closedBall, dist_zero_right]
    rw [hball]
    exact isCompact_closedBall (0 : E) 1
  let : TopologicalSpace O := I.adicTopology
  have hOtop : I.adicTopology =
      TopologicalSpace.induced (fun x : O ↦ (x : E)) inferInstance :=
    coefficientAdicTopology l E
  let : CompactSpace O := by
    change @CompactSpace O I.adicTopology
    rw [hOtop]
    exact hcompact
  have hOE : Continuous (fun x : O ↦ (x : E)) := by
    change @Continuous O E I.adicTopology _ (fun x ↦ (x : E))
    rw [hOtop]
    exact continuous_induced_dom
  let : TopologicalSpace Λ := I.adicModuleTopology Λ
  let : IsModuleTopology O Λ := adicFreeModuleTopology I
  let : ContinuousAdd Λ := IsModuleTopology.toContinuousAdd O Λ
  let : CompactSpace Λ := Module.Finite.compactSpace O Λ
  have hVt2 : T2Space V := by
    let b := Module.finBasis E V
    have hc : Continuous b.equivFun :=
      IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
    exact T2Space.of_injective_continuous b.equivFun.injective hc
  let : T2Space V := hVt2
  let : ContinuousSMul O V := ⟨by
    change Continuous (fun p : O × V ↦ (p.1 : E) • p.2)
    exact (hOE.comp continuous_fst).smul continuous_snd⟩
  have hcoe : Continuous (fun x : Λ ↦ (x : V)) :=
    IsModuleTopology.continuous_of_linearMap Λ.subtype
  exact (hcoe.isClosedEmbedding Subtype.val_injective).isEmbedding.isInducing.eq_induced



/-- A continuous action preserving a lattice restricts continuously to its adic topology.

Source: Stanford Weil II seminar, lecture 19, Proposition 1.1.9, p. 3.
(blueprint: lem-pod-profinite-stable-lattice-topology).

Proof: define the restricted action by applying the ambient automorphism and using stability to
construct the subtype witness.  The inclusion of the lattice into the ambient space is
continuous for the induced topology.  Rewriting the lattice topology by the supplied equality,
compose this inclusion with the jointly continuous ambient action. -/
private theorem stable_lattice_restricted_action_continuous
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (V : Type w) [AddCommGroup V] [Module E V] [FiniteDimensional E V] :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    letI : TopologicalSpace V := moduleTopology E V
    letI : Module (coefficientExtensionIntegers l E) V :=
      Module.compHom V (coefficientExtensionIntegers l E).subtype
    ∀ (ρ : G →* (V ≃ₗ[E] V)), Continuous (fun p : G × V ↦ ρ p.1 p.2) →
      ∀ Λ : Submodule (coefficientExtensionIntegers l E) V,
        (∀ g : G, (ρ g) '' (Λ : Set V) = (Λ : Set V)) →
        (coefficientExtensionMaximalIdeal l E).adicModuleTopology Λ =
          TopologicalSpace.induced (fun x : Λ ↦ (x : V)) inferInstance →
        letI := (coefficientExtensionMaximalIdeal l E).adicModuleTopology Λ
        ∃ a : G × Λ → Λ, Continuous a ∧
          ∀ p : G × Λ, (a p : V) = ρ p.1 (p.2 : V) := by
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let : TopologicalSpace V := moduleTopology E V
  intro ρ hρ Λ hstable htop
  let a : G × Λ → Λ := fun p ↦
    ⟨ρ p.1 (p.2 : V), by
      have hp : ρ p.1 (p.2 : V) ∈ (Λ : Set V) := by
        rw [← hstable p.1]
        exact ⟨(p.2 : V), p.2.property, rfl⟩
      exact hp⟩
  refine ⟨a, ?_, fun _ ↦ rfl⟩
  rw [htop]
  let : TopologicalSpace Λ := TopologicalSpace.induced
    (fun x : Λ ↦ (x : V)) (moduleTopology E V)
  apply continuous_induced_rng.mpr
  have hcoe : Continuous (fun x : Λ ↦ (x : V)) := continuous_induced_dom
  exact hρ.comp (continuous_fst.prodMk (hcoe.comp continuous_snd))



/-- The topological clauses for a finitely generated full stable lattice.

Source: Stanford Weil II seminar, lecture 19, Proposition 1.1.9, p. 3.
(blueprint: lem-pod-profinite-stable-lattice-topology).
The coefficient-ring coset basis identifies its adic topology with its compact spectral
subspace topology. Integral coordinates give the lattice its module topology and compactness.
Its continuous inclusion into the Hausdorff vector space is therefore an embedding. Finally
restrict the ambient continuous action, using stability to construct the subtype witness. -/
theorem stable_lattice_topology (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (V : Type w) [AddCommGroup V] [Module E V] [FiniteDimensional E V] :
    letI := spectralNorm.nontriviallyNormedField ℚ_[l] E
    letI : TopologicalSpace V := moduleTopology E V
    let O := coefficientExtensionIntegers l E
    letI : Module O V := Module.compHom V O.subtype
    ∀ (ρ : G →* (V ≃ₗ[E] V)), Continuous (fun p : G × V ↦ ρ p.1 p.2) →
      ∀ Λ : Submodule O V,
        Λ.FG → Submodule.span E (Λ : Set V) = ⊤ → Module.Free O Λ →
        Module.finrank O Λ = Module.finrank E V →
        (∀ g : G, (ρ g) '' (Λ : Set V) = (Λ : Set V)) →
        (coefficientExtensionMaximalIdeal l E).adicModuleTopology Λ =
          TopologicalSpace.induced (fun x : Λ ↦ (x : V)) inferInstance ∧
        (letI := (coefficientExtensionMaximalIdeal l E).adicModuleTopology Λ
         ∃ a : G × Λ → Λ, Continuous a ∧
           ∀ p : G × Λ, (a p : V) = ρ p.1 (p.2 : V)) := by
  dsimp
  intro ρ hρ Λ hfg _hspan hfree _hrank hstable
  have htop := stable_lattice_adic_topology_eq_induced l E V Λ hfg hfree
  refine ⟨htop, ?_⟩
  exact stable_lattice_restricted_action_continuous l E G V ρ hρ Λ hstable htop


end Padic
