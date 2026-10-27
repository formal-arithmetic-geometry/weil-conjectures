/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q79
-/
module

public import Sheaf.RepresentationTheory.LAdic
public import Sheaf.Topology.LadicLattice

import Sheaf.RepresentationTheory.ContinuousCoefficientSubquotients
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Dimension devissage for commuting ell-adic representations

Source: the agent-extracted dense-lattice argument in paragraph (3) of the blueprint's
`sk-thm-sf-ctf-stability-direct-images.proof.md`
(blueprint: lem-sfb-commuting-representation-devissage).

The lattice is written multiplicatively using its existing definition. Its ith generator
is the lift of `Pi.single i 1`, rather than the multiplicative identity (the zero vector).
Representations use the recorded finite-dimensional, jointly continuous coefficient predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u w

namespace Representation

open Profinite.LadicLattice

private theorem trivial_of_generators
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (r : ℕ)
    (V : Type w) [AddCommGroup V] [Module E V]
    (ρ : Lattice.{0} l r →* (V ≃ₗ[E] V))
    (hV : IsContinuousCoefficient l E (ProfiniteGrp.of (Lattice.{0} l r)) V ρ)
    (hgen : ∀ i : Fin r,
      (ρ (Multiplicative.ofAdd ⟨Pi.single i (1 : ℤ_[l])⟩)).toLinearMap -
        LinearMap.id = 0) :
    ∀ (g : Lattice.{0} l r) (v : V), ρ g v = v := by
  classical
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let : TopologicalSpace V := moduleTopology E V
  have : FiniteDimensional E V := hV.1
  have : T2Space V :=
    T2Space.of_injective_continuous (Module.finBasis E V).equivFun.injective
      (IsModuleTopology.continuous_of_linearMap (Module.finBasis E V).equivFun.toLinearMap)
  have hc : Continuous (fun p : Lattice.{0} l r × V ↦ ρ p.1 p.2) := hV.2
  have hgen' (i : Fin r) :
      ρ (Multiplicative.ofAdd ⟨Pi.single i (1 : ℤ_[l])⟩) = 1 := by
    ext v
    exact LinearMap.congr_fun (sub_eq_zero.mp (hgen i)) v
  have hsingle (i : Fin r) (a : ℤ_[l]) :
      ρ (Multiplicative.ofAdd ⟨Pi.single i a⟩) = 1 := by
    ext v
    refine PadicInt.denseRange_intCast.induction_on a ?_ ?_
    · apply isClosed_eq _ continuous_const
      have hι : Continuous (fun a : ℤ_[l] ↦
          (Multiplicative.ofAdd ⟨Pi.single i a⟩ : Lattice.{0} l r)) :=
        continuous_uliftUp.comp (continuous_single (A := fun _ : Fin r ↦ ℤ_[l]) i)
      exact hc.comp (hι.prodMk continuous_const)
    · intro z
      have hz : (Multiplicative.ofAdd ⟨Pi.single i (z : ℤ_[l])⟩ : Lattice.{0} l r) =
          (Multiplicative.ofAdd ⟨Pi.single i (1 : ℤ_[l])⟩) ^ z := by
        rw [← ofAdd_zsmul]
        congr 1
        apply ULift.ext
        funext j
        by_cases h : j = i <;> simp [h]
      simp [hz, map_zpow, hgen']
  intro g v
  have hsum : ∀ f : Fin r → ℤ_[l], ρ (Multiplicative.ofAdd ⟨f⟩) = 1 := by
    intro f
    apply Pi.single_induction (fun f ↦ ρ (Multiplicative.ofAdd ⟨f⟩) = 1) f
    · exact ρ.map_one
    · intro f g hf hg
      change ρ (Multiplicative.ofAdd ⟨f⟩ * Multiplicative.ofAdd ⟨g⟩) = 1
      rw [map_mul, hf, hg, one_mul]
    · exact hsingle
  exact DFunLike.congr_fun (hsum g.toAdd.down) v

/-- Extension-closed properties of continuous representations of the ell-adic lattice can be
checked on trivial representations and those with an invertible generator difference.

Source: blueprint direct-images proof paragraph (3), agent-formulated dimension-devissage
extraction (blueprint: lem-sfb-commuting-representation-devissage).

Proof plan:
1. The coefficient field is complete by `lem-weil-l-adic-extension-complete` and its norm
   is nontrivial since the norm of ell is ell inverse. Extend a basis of a stable subspace
   to one of the ambient space (`lem-weil-pbc-vector-space-basis-through-vector`). Both
   the subspace and quotient are finite-dimensional. The subspace topology is its usual
   module topology: a basis identification and its inverse are continuous by
   `lem-sfb-finite-dimensional-linear-map-continuous`. The restricted action is continuous.
   The extra basis vectors give a linear section of the quotient map. Both maps are
   continuous by the same lemma, so `(g,x) ↦ q (ρ g (s x))` gives the continuous quotient
   action. Equivariance of the canonical maps characterizes both actions uniquely.
2. Use strong induction on the dimension. Dimension zero is trivial. Rank zero gives
   the one-element group, so every action is trivial as well.
3. Put `A_i = T_i - id`. If all differences vanish, the image of the integer lattice acts
   trivially. That image is dense: finitely many prescribed ell-power residues have
   integer representatives coordinatewise. For every vector the stabilizer is closed,
   since its orbit map is continuous and its singleton is closed in the Hausdorff vector
   space. The stabilizer contains the dense integer lattice, so the action is trivial.
4. If some difference is invertible, apply the second hypothesis. Otherwise choose a
   nonzero singular difference. Its kernel is nonzero: injectivity would make the images
   of a basis a basis, by `lem-weil-pbc-vector-space-basis-through-vector`, hence make the
   difference invertible. The kernel is proper since the difference is nonzero.
5. All group elements commute with that difference, so its kernel is stable. Extend a
   kernel basis to an ambient basis by the same basis lemma. The kernel and quotient
   both have dimension strictly smaller than the ambient space.
6. Step 1 puts their induced actions in the class of continuous representations. Apply
   induction to both, then extension closure to the ambient representation. Equivariant
   isomorphism invariance removes dependence on choices of vector-space models. -/
theorem commuting_representation_devissage
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (E : IntermediateField ℚ_[l] Ω)
    [FiniteDimensional ℚ_[l] E] (r : ℕ)
    (P : ∀ (V : Type w) [AddCommGroup V] [Module E V],
      (Lattice.{0} l r →* (V ≃ₗ[E] V)) → Prop)
    (hiso : ∀ (V W : Type w) [AddCommGroup V] [Module E V]
      [AddCommGroup W] [Module E W]
      (ρ : Lattice.{0} l r →* (V ≃ₗ[E] V))
      (σ : Lattice.{0} l r →* (W ≃ₗ[E] W)),
      IsContinuousCoefficient l E (ProfiniteGrp.of (Lattice.{0} l r)) V ρ →
      IsContinuousCoefficient l E (ProfiniteGrp.of (Lattice.{0} l r)) W σ →
      ∀ e : V ≃ₗ[E] W, IsEquivariant E (Lattice.{0} l r) V W ρ σ e.toLinearMap →
        (P V ρ ↔ P W σ))
    (htrivial : ∀ (V : Type w) [AddCommGroup V] [Module E V]
      (ρ : Lattice.{0} l r →* (V ≃ₗ[E] V)),
      IsContinuousCoefficient l E (ProfiniteGrp.of (Lattice.{0} l r)) V ρ →
      (∀ (g : Lattice.{0} l r) (v : V), ρ g v = v) → P V ρ)
    (hinvertible : ∀ (V : Type w) [AddCommGroup V] [Module E V]
      (ρ : Lattice.{0} l r →* (V ≃ₗ[E] V)),
      IsContinuousCoefficient l E (ProfiniteGrp.of (Lattice.{0} l r)) V ρ →
      (∃ i : Fin r,
        IsUnit ((ρ (Multiplicative.ofAdd ⟨Pi.single i (1 : ℤ_[l])⟩)).toLinearMap -
          LinearMap.id)) → P V ρ)
    (hext : ∀ (V : Type w) [AddCommGroup V] [Module E V]
      (ρ : Lattice.{0} l r →* (V ≃ₗ[E] V)),
      IsContinuousCoefficient l E (ProfiniteGrp.of (Lattice.{0} l r)) V ρ →
      ∀ (U : Submodule E V)
        (_hU : ∀ (g : Lattice.{0} l r) (v : V), v ∈ U → ρ g v ∈ U)
        (τ : Lattice.{0} l r →* (U ≃ₗ[E] U))
        (κ : Lattice.{0} l r →* ((V ⧸ U) ≃ₗ[E] (V ⧸ U))),
        IsContinuousCoefficient l E (ProfiniteGrp.of (Lattice.{0} l r)) U τ →
        IsContinuousCoefficient l E (ProfiniteGrp.of (Lattice.{0} l r)) (V ⧸ U) κ →
        IsEquivariant E (Lattice.{0} l r) U V τ ρ U.subtype →
        IsEquivariant E (Lattice.{0} l r) V (V ⧸ U) ρ κ U.mkQ →
        P U τ → P (V ⧸ U) κ → P V ρ)
    (W : Type w) [AddCommGroup W] [Module E W]
    (ρ : Lattice.{0} l r →* (W ≃ₗ[E] W))
    (hW : IsContinuousCoefficient l E (ProfiniteGrp.of (Lattice.{0} l r)) W ρ) :
    P W ρ := by
  classical
  have _ := hiso
  have hall : ∀ n (V : Type w) [AddCommGroup V] [Module E V]
      (σ : Lattice.{0} l r →* (V ≃ₗ[E] V))
      (hV : IsContinuousCoefficient l E (ProfiniteGrp.of (Lattice.{0} l r)) V σ),
      Module.finrank E V = n → P V σ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ _ σ hV hdim
      have : FiniteDimensional E V := hV.1
      by_cases hinv : ∃ i : Fin r,
          IsUnit ((σ (Multiplicative.ofAdd ⟨Pi.single i (1 : ℤ_[l])⟩)).toLinearMap -
            LinearMap.id)
      · exact hinvertible V σ hV hinv
      by_cases hz : ∀ i : Fin r,
          (σ (Multiplicative.ofAdd ⟨Pi.single i (1 : ℤ_[l])⟩)).toLinearMap -
            LinearMap.id = 0
      · exact htrivial V σ hV (trivial_of_generators l E r V σ hV hz)
      push Not at hz
      obtain ⟨i, hi⟩ := hz
      let t : Lattice.{0} l r := Multiplicative.ofAdd ⟨Pi.single i (1 : ℤ_[l])⟩
      let A : V →ₗ[E] V := (σ t).toLinearMap - LinearMap.id
      let U : Submodule E V := LinearMap.ker A
      have hbot : U ≠ ⊥ := by
        intro h
        exact hinv ⟨i, (LinearMap.isUnit_iff_ker_eq_bot A).mpr h⟩
      have htop : U ≠ ⊤ := by
        intro h
        apply hi
        apply LinearMap.ext
        intro v
        have hv : v ∈ U := h.symm ▸ Submodule.mem_top
        exact hv
      have hstable : ∀ (g : Lattice.{0} l r) (v : V), v ∈ U → σ g v ∈ U := by
        intro g v hv
        change σ t v - v = 0 at hv
        change σ t (σ g v) - σ g v = 0
        have hc : σ t (σ g v) = σ g (σ t v) := by
          rw [← LinearEquiv.mul_apply, ← map_mul, mul_comm t g,
            map_mul, LinearEquiv.mul_apply]
        rw [hc, sub_eq_zero.mp hv, sub_self]
      have hdimU : Module.finrank E U < n := by
        rw [← hdim]
        exact Submodule.finrank_lt htop
      have hdimQ : Module.finrank E (V ⧸ U) < n := by
        have hpos : 0 < Module.finrank E U := by
          by_contra h
          exact hbot (Submodule.finrank_eq_zero.mp (by omega))
        have hsum := U.finrank_quotient_add_finrank
        omega
      let := spectralNorm.nontriviallyNormedField ℚ_[l] E
      let : TopologicalSpace V := moduleTopology E V
      obtain ⟨_, _, _, τ, κ, hτ, hκ, _, _, heqτ, _, heqκ, _⟩ :=
        (continuousCoefficient_subquotients.{u, 0, w, w, w, w} l Ω E rfl
          (ProfiniteGrp.of (Lattice.{0} l r)) V σ hV).1 U hstable
      exact hext V σ hV U hstable τ κ hτ hκ heqτ heqκ
        (ih (Module.finrank E U) hdimU U τ hτ rfl)
        (ih (Module.finrank E (V ⧸ U)) hdimQ (V ⧸ U) κ hκ rfl)
  exact hall (Module.finrank E W) W ρ hW rfl

end Representation
