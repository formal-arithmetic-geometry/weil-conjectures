/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleExchange
public import WeilConjectures.TraceFormula.Basic
public import WeilConjectures.TraceFormula.Specialization.NearbyFiniteness
public import WeilConjectures.TraceFormula.Specialization.TraitHigherDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnitSingle

/-!

# Nearby cycles of the trait itself

The trait `S = Spec k'⟦t⟧` is a model of the base point `Spec k` with special fibre `Spec k'`
(`ProEtale.CondensedRing.traitModel`): its geometric generic fibre `Spec Ω` maps to `Spec k`.
Its nearby cycles `Ψ_s` on bounded constructible complexes
(`ProEtale.CondensedRing.traitSpecialization`) are the target of the dualizing maps
`θ_X : Ψ_X ω_X ⟶ ω_{X'}`, which are read through the specialization unit `σ_s : ℚ̄_ℓ ⟶ Ψ_s ℚ̄_ℓ`
(`ProEtale.CondensedRing.traitSpecializationUnit`).

## Implementation notes

Nothing uses these declarations yet. They are the base point of the compact-support exchange
`ν_{a_X}` of the structure map `a_X : X ⟶ Spec k`, which builds the dualizing maps `θ_X` from the
exceptional exchange `β_{a_X}` (`ProEtale.CondensedRing.dualizingExchange` takes `σ_s` as a
parameter). Reading `θ_X` through `σ_s⁻¹` needs `σ_s` to be an isomorphism
(`ProEtale.CondensedRing.isIso_traitSpecializationUnit`), the point case of blueprint
`det-sp-constant-family-vanishing`. It follows from the pro-étale computations over the strictly
henselian trait that `i^*` inverts the unit `ℚ̄_ℓ ⟶ j_* ℚ̄_ℓ` and kills `Rⁿ j_* ℚ̄_ℓ` for `n > 0`
(`WeilConjectures.TraceFormula.Specialization.TraitDirectImageUnit`,
`WeilConjectures.TraceFormula.Specialization.TraitHigherDirectImage`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Unit

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end Unit

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

end AlgebraicGeometry.ProEtale.CondensedRing
