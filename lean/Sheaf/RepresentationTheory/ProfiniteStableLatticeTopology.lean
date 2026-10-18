module

public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Topology.Algebra.Group.Basic

@[expose] public section

universe u v w

namespace Padic

/-- The topological clauses for a finitely generated full stable lattice.

Source: Stanford Weil II seminar, lecture 19, Proposition 1.1.9, p. 3.
(blueprint: lem-pod-profinite-stable-lattice-topology).
An integral basis identifies the lattice with a finite product of the coefficient ring;
the powers of the maximal ideal give both the adic and subspace neighborhood bases, and
the restricted action is the restriction of the ambient continuous action. -/
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
  sorry

end Padic
