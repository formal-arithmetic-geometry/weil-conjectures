/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGlobal
public import WeilConjectures.TraceFormula.Specialization.TraitModelOfGenericBase
public import WeilConjectures.TraceFormula.Specialization.TraitNearbyFiniteness

/-!

# The trait as a model of a point

Let `S = Spec k'⟦t⟧` be the strictly henselian trait, `Spec Ω` its geometric generic point and
`ε : Spec Ω ⟶ Spec F` a morphism to the spectrum of a field `F`. The trait is a model of the
point `Spec F` with special fibre `Spec k'` (`ProEtale.CondensedRing.traitModelOfPoint`): its
geometric generic fibre `Spec Ω` maps to `Spec F` by `ε`. The trait model of the base point
(`ProEtale.CondensedRing.traitModel`), for `F` mapping into `k'⟦t⟧`, is definitionally
`traitModelOfPoint (traitModel k k').ε`. For `ε` factoring as `Spec Ω ⟶ η ⟶ Spec F` through the
generic point `η = Spec Frac k'⟦t⟧` (`ProEtale.CondensedRing.traitModelOfGenericBase`), it is a
trait model over the generic base `(F, Spec F)`
(`ProEtale.CondensedRing.isTraitModelOfGenericBase_traitModelOfGenericBase`).

* Its nearby cycles preserve bounded constructible complexes
  (`ProEtale.CondensedRing.preservesBoundedConstructible_traitModelOfPoint`): the pullback
  `Lε^* K` to `Spec Ω` is bounded constructible, and the nearby functor `Li^* Rj_*` of the trait
  carries bounded constructible complexes on `Spec Ω` to bounded constructible complexes
  (`ProEtale.CondensedRing.boundedConstructible_traitNearby_singleFunctor_obj`, by dévissage).
  Unlike `NearbyCyclesModel.preservesBoundedConstructible_of_isTraitModel`, this does not need `ε`
  to factor through the total space.
* Its specialization unit `σ : ℚ̄_ℓ ⟶ Ψ ℚ̄_ℓ` is an isomorphism
  (`ProEtale.CondensedRing.isIso_traitPointSpecializationUnit`), as it only involves `j` and `i`.
* Its nearby cycles are monoidal (`NearbyCyclesModel.exists_monoidal_traitPointSpecialization`),
  and its duality map with dualizing map `σ⁻¹` is an isomorphism
  (`NearbyCyclesModel.isIso_nearbyDualityMap_traitModelOfPoint`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

section Model

variable {F : Type u} [Field F] {k' : Type u} [Field k']
  (ε : Spec (.of (traitGenericField k')) ⟶ Spec (.of F))

variable (F) (ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F))

end Model

section BoundedConstructible

variable {F : Type u} [Field F] {k' : Type u} [Field k'] [IsSepClosed k']
  (ε : Spec (.of (traitGenericField k')) ⟶ Spec (.of F)) (ℓ : ℕ) [Fact ℓ.Prime]

variable [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]

end BoundedConstructible

namespace NearbyCyclesModel

section Monoidal

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {F : Type u} [Field F] {k' : Type u} [Field k'] [IsSepClosed k']
  (ε : Spec (.of (traitGenericField k')) ⟶ Spec (.of F))

end Monoidal

variable (ℓ : ℕ) [Fact ℓ.Prime] {F : Type u} [Field F] [Fact (ringChar F).Prime]
  [Fact (ringChar F ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [IsSepClosed k']
  (ε : Spec (.of (traitGenericField k')) ⟶ Spec (.of F))

end NearbyCyclesModel

section TraitModel

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']

variable (ℓ : ℕ) [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]

end TraitModel

end AlgebraicGeometry.ProEtale.CondensedRing
