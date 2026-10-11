/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.NumberTheory.Padics.CoefficientExtension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Stable lattices for compact groups

Source: Stanford Weil II seminar, lecture 19 (D. Dore), Proposition 1.1.9, pp. 2–3
(blueprint: lem-pod-profinite-stable-lattice).
-/

universe u v w

namespace Padic

/-- Every jointly continuous linear representation of a compact group over a finite extension
of `ℚ_[l]` preserves a finite free lattice of the expected rank. Its maximal-ideal-adic
and subspace topologies agree, and the restricted action is continuous.

Source: Stanford Weil II seminar, lecture 19 (D. Dore), Proposition 1.1.9, pp. 2–3
(blueprint: lem-pod-profinite-stable-lattice).

Proof: choose a basis and its integer span `Λ₀`. Its stabilizer is open by
`lem-pod-lattice-stabilizer-open`; evaluation on basis vectors shows the representation is
continuous, hence its inverse-image stabilizer `H` is open. Compactness gives finitely many
cosets `gᵢ H`. Take the sum of the translates `ρ(gᵢ) Λ₀`. This is finitely generated, spans,
and is torsion-free; the DVR result `lem-sc-dvr-fg-torsionfree-free` makes it free of rank
`dim V`. Left multiplication permutes these translates, so the sum is stable (apply the
inclusion also to the inverse to get equality). Restrict the original action to the sum.
An integer basis identifies the lattice with `𝒪_E^r` inside `E^r`; the powers of the maximal
ideal give the same neighborhood basis as the subspace topology, proving the final clauses. -/
theorem exists_stable_lattice (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
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
        (∀ g : G, (ρ g) '' (Λ : Set V) = (Λ : Set V)) ∧
        (coefficientExtensionMaximalIdeal l E).adicModuleTopology Λ =
          TopologicalSpace.induced (fun x : Λ ↦ (x : V)) inferInstance ∧
        (letI := (coefficientExtensionMaximalIdeal l E).adicModuleTopology Λ
         ∃ a : G × Λ → Λ, Continuous a ∧
           ∀ p : G × Λ, (a p : V) = ρ p.1 (p.2 : V)) := by
  sorry

end Padic
