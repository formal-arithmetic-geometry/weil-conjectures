/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationData
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationFunctor
public import WeilConjectures.Mathlib.RepresentationTheory.Irreducible
public import WeilConjectures.RepresentationTheory.WeilGroupTwist
public import WeilConjectures.WeilSheaf.LisseFiltration

/-!
# Monodromy of irreducible lisse Weil sheaves and Weil II 1.3.14

Let `C₀` be a curve over the finite field `K` with Weil group `W`, base point data `B` and a
monodromy `M` of lisse sheaves on the geometric curve which is an equivalence at the base point
(`AlgebraicGeometry.ProEtale.LisseMonodromy.IsEquivalenceAt`), together with the homotopy exact
sequence input `D` (`AlgebraicGeometry.WeilGroup.WeilMonodromyData`). A lisse Weil sheaf `ℱ`
then has a Weil fundamental representation `ρ_ℱ` of `W` on its stalk `ℱ_t`
(`AlgebraicGeometry.WeilGroup.fundamentalRep`).

We show:

* `AlgebraicGeometry.WeilGroup.isIrreducible_fundamentalRep`: if `ℱ` is irreducible lisse, then
  `ρ_ℱ` is an irreducible representation. A `W`-stable subspace `U ⊆ ℱ_t` is the Weil fundamental
  representation of a lisse Weil sheaf `𝒢`, and the inclusion is the stalk of a morphism
  `𝒢 ⟶ ℱ`, which is a monomorphism of Weil sheaves since the stalk functor is faithful and
  lisse sheaves are closed under kernels. Conversely
  (`AlgebraicGeometry.WeilGroup.isIrreducibleLisse_iff_isIrreducible_fundamentalRep`), a lisse
  Weil sheaf with irreducible Weil fundamental representation is irreducible lisse.
* `AlgebraicGeometry.WeilGroup.isBoundedOn_fundamentalRep_geometric`: `ρ_ℱ` is bounded on the
  geometric fundamental group `ker deg`, which is compact and acts continuously.
* `AlgebraicGeometry.WeilGroup.exists_isBoundedOn_twist_fundamentalRep` (**Deligne, Weil II,
  1.3.14**): for irreducible lisse `ℱ` there is `b ∈ ℚ̄_ℓˣ` such that the twist
  `ρ_ℱ ⊗ b^{-deg}` is bounded on all of `W`; and
  `AlgebraicGeometry.WeilGroup.exists_isBoundedOn_fundamentalRep_twist`: this twist is the Weil
  fundamental representation of an irreducible lisse Weil sheaf `ℱ'`, so `ℱ` is the twist of
  an irreducible lisse Weil sheaf with bounded (i.e. integral, "étale") monodromy.
* `AlgebraicGeometry.WeilGroup.exists_finite_range_twist_fundamentalRep`: finite geometric
  monodromy becomes finite monodromy after a twist, and
  `AlgebraicGeometry.WeilGroup.finrank_eq_one_and_exists_twist_eq_one_fundamentalRep`: trivial
  geometric monodromy forces rank one and `ρ_ℱ = b ^ deg`.

For geometrically constant sheaves the sheaf-level statement is
`AlgebraicGeometry.WeilSheaf.exists_iso_constantTwist_of_isGeometricallyConstant`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace Representation

section Continuous

variable {k G V : Type*} [NormedField k] [Group G] [AddCommGroup V] [Module k V]

end Continuous

section Subrepresentation

variable {k G H V : Type*} [Field k] [TopologicalSpace k] [Monoid G] [Monoid H]
  [TopologicalSpace H] [AddCommGroup V] [Module k V]

/-- A subrepresentation of a representation continuous along `ι` is continuous along `ι`: a
linear form on the subspace extends to the whole space. -/
theorem IsContinuousOn.subrepresentation {ι : H →* G} {ρ : Representation k G V}
    (hρ : ρ.IsContinuousOn ι) (U : Subrepresentation ρ) : U.toRepresentation.IsContinuousOn ι := by
  intro φ v
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend φ
  have (h : H) : φ (U.toRepresentation (ι h) v) = ψ (ρ (ι h) v) := by
    rw [← hψ]
    rfl
  simp_rw [this]
  exact hρ ψ v

end Subrepresentation

section Irreducible

variable {k G V V' : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup V']
  [Module k V']

/-- Irreducibility is transported along an intertwining linear equivalence. -/
theorem IsIrreducible.of_linearEquiv {ρ : Representation k G V} {ρ' : Representation k G V'}
    [ρ.IsIrreducible] (e : V' ≃ₗ[k] V) (he : ∀ g v, e (ρ' g v) = ρ g (e v)) :
    ρ'.IsIrreducible := by
  obtain ⟨hV, h⟩ := isIrreducible_iff.1 ‹ρ.IsIrreducible›
  refine isIrreducible_iff.2 ⟨e.symm.injective.nontrivial, fun U hU ↦ ?_⟩
  have hU' := h (U.map e.toLinearMap) fun g v hv ↦ by
    obtain ⟨u, hu, rfl⟩ := hv
    exact ⟨ρ' g u, hU g u hu, he g u⟩
  rw [← Submodule.comap_map_eq_of_injective e.injective U]
  refine hU'.imp (fun h₀ ↦ ?_) fun h₀ ↦ ?_
  · rw [h₀, Submodule.comap_bot]
    exact LinearEquiv.ker _
  · rw [h₀, Submodule.comap_top]

/-- The twist of an irreducible representation by a character is irreducible: both have the same
invariant subspaces. -/
theorem IsIrreducible.twist {ρ : Representation k G V} [ρ.IsIrreducible] (χ : G →* kˣ) :
    (ρ.twist χ).IsIrreducible := by
  obtain ⟨hV, h⟩ := isIrreducible_iff.1 ‹ρ.IsIrreducible›
  refine isIrreducible_iff.2 ⟨hV, fun U hU ↦ h U fun g v hv ↦ ?_⟩
  have : ρ g v = ((χ g : kˣ) : k)⁻¹ • ρ.twist χ g v := by
    rw [twist_apply, LinearMap.smul_apply, inv_smul_smul₀ (Units.ne_zero _)]
  rw [this]
  exact U.smul_mem _ (hU g v hv)

end Irreducible

end Representation

namespace AlgebraicGeometry.WeilGroup

open ProEtale Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
  [IsCurve (C ↘ Spec (.of K))] {W : WeilGroup (C ↘ Spec (.of K))}
  {M : LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber K} {B : BasePointData W}

section StalkMap

end StalkMap

section Irreducible

variable (M)

end Irreducible

section Twist

variable (M) (D : WeilMonodromyData B)

end Twist

end AlgebraicGeometry.WeilGroup
