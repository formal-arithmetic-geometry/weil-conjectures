module

public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Topology.Algebra.Group.Basic
import Sheaf.NumberTheory.Padics.LatticeStabilizerOpen

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
  sorry

end Padic
