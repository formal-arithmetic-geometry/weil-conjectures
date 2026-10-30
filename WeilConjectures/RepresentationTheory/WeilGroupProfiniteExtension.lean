/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RepresentationTheory.FiniteDimensionalRealization
public import WeilConjectures.RepresentationTheory.WeilGroupLattice

/-!
# Bounded representations of a dense Weil group extend to the profinite group

Let `ι : W → Π` be a homomorphism with dense image from a group `W` with a degree
`deg : W → ℤ` into a profinite group `Π` (for instance the Weil group `π₁(X, t) ⋊ ℤ` of a scheme
`X₀` over a finite field inside its arithmetic fundamental group `π₁(X₀)`), such that the
geometric part `ker deg = κ(G)`, `G` compact, embeds into `Π`, and such that the degree is
continuous for the topology induced by `Π`. Then a finite-dimensional `ℚ̄_ℓ`-representation of `W`
which is continuous on `G` and bounded on `W` extends to a continuous representation of `Π`
(Deligne, Weil II, 1.3.14 and 1.1.7): it stabilises a lattice (`MonoidHom.exists_lattice_of_isWeaklyBounded_of_compactSpace`), its
reductions modulo `ℓᵏ` factor through open subgroups of `Π`, and the closure of its graph is the
graph of a continuous extension.

## Main results

* `MonoidHom.exists_continuous_extend_of_forall_nhds_one`: a homomorphism `f : W → M` to a
  compact Hausdorff topological monoid which is continuous at `1` for the topology induced by
  a dense `ι : W → Π`, `Π` compact, extends to a continuous homomorphism `Π → M` (closed graph).
* `Representation.exists_extension_of_isBoundedOn`: the extension of bounded representations.
-/

@[expose] public section

open Topology

namespace MonoidHom

/-- **Extension of homomorphisms from a dense subgroup** (closed graph argument). Let
`ι : W →* Π` have dense range in a compact Hausdorff group `Π`, and let `f : W →* M` be a
homomorphism to a compact Hausdorff topological monoid which is continuous at `1` for the
topology induced by `ι`: for every neighbourhood `V` of `1` in `M` there is a neighbourhood `U` of
`1` in `Π` with `f w ∈ V` whenever `ι w ∈ U`. Then `f` extends to a continuous homomorphism
`F : Π →* M`, `F ∘ ι = f`. -/
theorem exists_continuous_extend_of_forall_nhds_one {W P M : Type*} [Group W] [Group P]
    [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [Monoid M]
    [TopologicalSpace M] [ContinuousMul M] [CompactSpace M] [T2Space M] (ι : W →* P)
    (hι : DenseRange ι) (f : W →* M)
    (hf : ∀ V ∈ 𝓝 (1 : M), ∃ U ∈ 𝓝 (1 : P), ∀ w, ι w ∈ U → f w ∈ V) :
    ∃ F : P →* M, Continuous F ∧ ∀ w, F (ι w) = f w := by
  sorry

end MonoidHom

namespace Representation

/-- **Bounded representations of a dense Weil group extend to the profinite group** (Deligne,
Weil II, 1.3.14 and 1.1.7). Let `ι : W →* Π` have dense range in a profinite group `Π`, let
`deg : W →* ℤ` have an element `γ` of degree one, and let `κ : G →* W` be a homomorphism from a
compact Hausdorff group onto `ker deg` such that `ι ∘ κ` is continuous and injective. Assume
that the degree is continuous for the topology induced by `Π`: for every `M > 0` there is a
neighbourhood `U` of `1` such that `M ∣ deg w` whenever `ι w ∈ U`. Then every finite-dimensional
representation `ρ` of `W` over `ℚ̄_ℓ` which is continuous along `κ` and bounded on `W` extends to a
continuous representation `τ` of `Π`: `τ ∘ ι = ρ`. -/
theorem exists_extension_of_isBoundedOn {ℓ : ℕ} [Fact ℓ.Prime] {W P G V : Type*} [Group W]
    [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P] [T2Space P]
    [TotallyDisconnectedSpace P] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    [FiniteDimensional (PadicAlgCl ℓ) V] {deg : W →* Multiplicative ℤ} {γ : W}
    (hγ : deg γ = Multiplicative.ofAdd 1) (κ : G →* W) (hκdeg : ∀ g, deg (κ g) = 1)
    (hκ : ∀ w, deg w = 1 → ∃ g, κ g = w) (ι : W →* P) (hι : DenseRange ι)
    (hικ : Continuous (ι.comp κ)) (hικ' : Function.Injective (ι.comp κ))
    (hdeg : ∀ M : ℕ, 0 < M → ∃ U ∈ 𝓝 (1 : P), ∀ w, ι w ∈ U →
      (M : ℤ) ∣ Multiplicative.toAdd (deg w))
    (ρ : Representation (PadicAlgCl ℓ) W V) (hcont : ρ.IsContinuousOn κ)
    (hb : ρ.IsBoundedOn Set.univ) :
    ∃ τ : Representation (PadicAlgCl ℓ) P V, (∀ w, τ (ι w) = ρ w) ∧
      ∀ (φ : Module.Dual (PadicAlgCl ℓ) V) (v : V), Continuous fun x ↦ φ (τ x v) := by
  sorry

end Representation
