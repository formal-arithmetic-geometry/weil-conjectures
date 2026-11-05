/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.TraitChange
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModel

/-!

# Invariance of nearby cycles under the change of trait `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧`

For separably closed fields `k' ⊆ K`, the change of trait `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧`
(`AlgebraicGeometry.traitMap`) is a morphism of strictly henselian traits. The invariance of
nearby cycles under change of strictly henselian trait
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait`, SGA 4½,
[Th. finitude], Prop. 3.7) therefore applies to the base change `M ×_S Spec K⟦t⟧` of a model of
finite type over `S = Spec k'⟦t⟧`
(`NearbyCyclesModel.isIso_pullbackExchange_baseChangeHom_traitMap_of_generic`). This is the
first "fact about traits" of the blueprint proof of `sk-prop-tf-nearby-external-kunneth`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

variable (k' : Type u) [Field k'] (K : Type u) [Field K] [Algebra k' K]

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] {X : Scheme.{u}}
  {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g)

variable [IsSepClosed k'] [IsSepClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k' ≠ ℓ)]

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
