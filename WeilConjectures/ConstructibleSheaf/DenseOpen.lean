/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Finite locally constant sheaves extend uniquely from a dense open of a normal scheme

Let `X` be a locally Noetherian scheme whose local rings are integrally closed domains, and let
`k : V ⟶ X` be an open immersion with dense range. A finite locally constant sheaf `N` on the
small étale site of `X` is the direct image of its restriction to `V`: the unit
`N ⟶ k_* k^* N` of the adjunction `k^* ⊣ k_*` is an isomorphism.

## Main statements

- `AlgebraicGeometry.Scheme.isIso_unit_upperStarLowerStarAdjunction_of_isIntegrallyClosed`

## Implementation notes

Mathlib has no notion of a normal scheme, so normality of `X` is spelled out as the two
instance hypotheses that every local ring `𝒪_{X,x}` is a domain and is integrally closed.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme


variable {V X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- Blueprint `lem-wf-dense-open-pi1-surjective`, part (3): Fundamental groups of a dense open
surject.

Let `X` be a normal locally Noetherian scheme and `k : V ⟶ X` an open immersion with dense
range. Every finite locally constant sheaf `N` on `X` extends uniquely from `V`: the unit
`N ⟶ k_* k^* N` of `k^* ⊣ k_*` is an isomorphism.

On an étale `T ⟶ X` the sections of `N` are, componentwise on the finitely many normal
integral components `Tᵢ` of `T`, the invariants of the fundamental group `π₁(Tᵢ)` on a
geometric stalk, and the sections of `k_* k^* N` are the invariants of `π₁(Tᵢ ×_X V)`; both
groups have the same image because `π₁(Tᵢ ×_X V) ⟶ π₁(Tᵢ)` is surjective (part (1)). For a
smooth curve this recovers `lem-a1-lisse-middle-extension`. -/
theorem isIso_unit_upperStarLowerStarAdjunction_of_isIntegrallyClosed [IsLocallyNoetherian X]
    [∀ x : X, IsDomain (X.presheaf.stalk x)] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (k : V ⟶ X) [IsOpenImmersion k] (hk : Dense (Set.range k.base))
    (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf N] :
    IsIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) k).unit.app N) := by
  sorry

end AlgebraicGeometry.Scheme
