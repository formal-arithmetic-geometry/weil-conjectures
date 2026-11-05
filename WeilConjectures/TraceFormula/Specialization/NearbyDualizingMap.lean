/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Verdier
public import WeilConjectures.TraceFormula.Specialization.PointModel

/-!

# The dualizing maps of nearby cycles over the trait

Let `S = Spec k'⟦t⟧` be the strictly henselian trait, `k'` separably closed. A model `M` of a
separated `k`-scheme `X` of finite type is a *trait model of `X` over the base*
(`NearbyCyclesModel.IsTraitModelOfBase`) if it is of finite type over `S` along `q : 𝒳 ⟶ S`,
its identification `ε : 𝒳_Ω ⟶ X` factors through a `k`-morphism `𝒳 ⟶ X` (`𝒳` being a `k`-scheme
through `q` and `S ⟶ Spec k`), and its geometric generic fibre
is the base change `X ×_k Spec Ω`. Such a model maps to the trait model of the point
(`ProEtale.CondensedRing.traitModel`) over the structure morphisms
(`NearbyCyclesModel.IsTraitModelOfBase.toTrait`), with proper exchange
`χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_X` (`NearbyCyclesModel.IsTraitModelOfBase.pushforwardExchange`).

The *dualizing map* `θ_X : Ψ_X ω_X ⟶ ω_{X'}` (blueprint `det-nearby-exchange-maps` (5),
`θ_X = β_{a_X}(A)`) is the exceptional adjoint of the compact-support exchange `ν_{a_X}`, read
through the specialization unit of the trait and the base change `Lε^* ω_{X/k} ≅ ω_{𝒳_Ω/Ω}`.
The compact-support exchange is built from a relative compactification of `𝒳` over `S`, and is
independent of the choice (`NearbyCyclesModel.IsTraitModelOfBase.dualizingMap`, downstream).
A family of maps `θ` with the two properties
that characterize the dualizing maps is a `NearbyCyclesModel.NearbyDualizingData`, and its
existence is the node lemma `NearbyCyclesModel.nonempty_nearbyDualizingData` (blueprint
`det-nearby-exchange-maps` and the composition law `sk-lem-tf-nearby-mate-coherences` (4)):

* **proper models**: for `q` proper and geometric generic fibre all of `X ×_k Spec Ω`,
  `ν_{a} = χ_a⁻¹` under `Ra_! ≅ Ra_*`, so `θ_X` is the unique
  map with `tr_{X'} ∘ Ra'_*(θ_X) ∘ χ_a(ω_X) = σ⁻¹ ∘ Ψ_S(tr_X)`, `tr` the traces
  `Ra_* ω_X ≅ Ra_! Ra^! ℚ̄_ℓ ⟶ ℚ̄_ℓ` (`NearbyCyclesModel.trace`) and `σ` the specialization unit
  of the trait;
* **open restriction**: for an open sub-model `N ⊆ M` over open immersions `j`, `j'`,
  `θ_N = j'^* θ_M ∘ β_j(ω_X)` with `β_j = α_j⁻¹` and `j^! = j^*`, that is
  `ρ' ∘ j'^*(θ_M) = θ_N ∘ Ψ_N(ρ) ∘ α_j(ω_X)` for the identifications `ρ : j^* ω_X ≅ ω_Y`.

These two properties determine the family `θ`: every trait model is an open sub-model of a proper
one whose geometric generic fibre is all of `X̄ ×_k Spec Ω`
(`NearbyCyclesModel.IsTraitModelOfBase.exists_isProper_openSubmodel`), the proper exchange `χ_a`
is then invertible, and maps
`A ⟶ ω_{X'}` are determined by their traces.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (k : Type u) [Field k] {k' : Type u} [Field k'] [Algebra k k']

variable {k} {X : Over (Spec (.of k))} {X' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

namespace IsTraitModelOfBase

end IsTraitModelOfBase

variable (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

/-- The trace `tr_X : Ra_* ω_X ≅ Ra_! Ra^! ℚ̄_ℓ ⟶ ℚ̄_ℓ` of a proper `k`-scheme: the counit of
`Ra_! ⊣ Ra^!` read through `Ra_! ≅ Ra_*`. -/
noncomputable def trace (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom]
    [QuasiCompact Z.hom] [IsSeparated Z.hom] [IsProper (toPoint Z).left] :
    (boundedConstructibleLowerStar ℓ (toPoint Z)).obj
        (dualizingComplex ℓ Z) ⟶ 𝟙_ _ :=
  (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Z)).inv.app _ ≫
    (boundedConstructibleUpperShriekAdjunction ℓ (toPoint Z)).counit.app (𝟙_ _)

variable (k k')

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
