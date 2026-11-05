/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingUnique
public import WeilConjectures.TraceFormula.Specialization.TraitModelGenericPoint
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBaseFiniteness

/-!

# The dualizing maps of nearby cycles over a generic base

Let `S = Spec k'⟦t⟧` be the strictly henselian trait, `k'` separably closed, and `M` a trait model
of an `F`-scheme `X₁` over the generic base `(F, X₁)` along `ι : η ⟶ Spec F`
(`NearbyCyclesModel.IsTraitModelOfGenericBase`). For every `ε₀ : Spec Ω ⟶ Spec F` with
`g ≫ ε₀ = ε ≫ (X₁ ⟶ Spec F)`, the model maps to the trait as a model of the point `Spec F` along
`ε₀` (`ProEtale.CondensedRing.traitModelOfPoint`) over the structure morphisms
(`NearbyCyclesModel.IsTraitModelOfGenericBase.toPoint`), with proper exchange
`χ_a : Ψ_S Ra_* ⟶ Ra'_* Ψ_X` (`NearbyCyclesModel.IsTraitModelOfGenericBase.pushforwardExchange`).

A *family of dualizing maps over a generic base*
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase`) is a map `θ_M : Ψ_M ω_{X₁} ⟶ ω_{X'}` for
every trait model over a generic base, with the trace property for proper models with full
generic fibre and the open restriction property, as for the dualizing maps of trait models over
a base field (`NearbyCyclesModel.NearbyDualizingData`). Its existence is the node lemma
`NearbyCyclesModel.nonempty_nearbyDualizingDataOfGenericBase`, proved downstream in
`TraceFormula.Specialization.NearbyDualizingGenericBaseExistence` from the compact-support
exchanges of compactifications. It restricts to a family of dualizing maps
over every base field `k` of `k'`
(`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.toNearbyDualizingData`), so that it agrees
with every such family (`NearbyCyclesModel.NearbyDualizingDataOfGenericBase.θ_eq_θ`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

section Hom

variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

variable (ℓ : ℕ) [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar F).Prime]
  [Fact (ringChar F ≠ ℓ)] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]

end Hom

variable (k' : Type u) [Field k'] (ℓ : ℕ) [Fact ℓ.Prime] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

namespace NearbyDualizingDataOfGenericBase

variable {k' ℓ} (D : NearbyDualizingDataOfGenericBase k' ℓ)
  (k : Type u) [Field k] [Algebra k k'] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

end NearbyDualizingDataOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
