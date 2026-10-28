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
(`NearbyCyclesModel.isIso_pullbackExchange_baseChangeHom_traitMap`). This is the first "fact about
traits" of the blueprint proof of `sk-prop-tf-nearby-external-kunneth`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

variable (k' : Type u) [Field k'] (K : Type u) [Field K] [Algebra k' K]

/-- The coefficientwise map `k'⟦t⟧ ⟶ K⟦t⟧` is a local homomorphism. -/
instance isLocalHom_powerSeriesMap :
    IsLocalHom (PowerSeries.map (algebraMap k' K)) where
  map_nonunit p hp := by
    rw [PowerSeries.isUnit_iff_constantCoeff] at hp ⊢
    rw [constantCoeff_map_apply] at hp
    exact isUnit_iff_ne_zero.mpr fun h ↦ by simp [h] at hp

/-- The map `k'⟦t⟧ ⟶ (Frac k'⟦t⟧)^alg` to the field of the geometric generic point is
injective. -/
lemma algebraMap_traitGenericField_injective :
    Function.Injective (algebraMap (PowerSeries k') (traitGenericField k')) := by
  rw [IsScalarTower.algebraMap_eq (PowerSeries k') (FractionRing (PowerSeries k'))]
  exact (algebraMap (FractionRing (PowerSeries k')) (traitGenericField k')).injective.comp
    (IsFractionRing.injective _ _)

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] {X : Scheme.{u}}
  {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g)

variable [IsSepClosed k'] [IsSepClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k' ≠ ℓ)]

include hM in
/-- **Invariance of nearby cycles under change of trait** (SGA 4½, [Th. finitude], Prop. 3.7;
blueprint `sk-prop-tf-nearby-external-kunneth`, "Facts about traits", first fact): for a model `M`
of finite type over the strictly henselian trait `S = Spec k'⟦t⟧` and the change of trait
`Spec K⟦t⟧ ⟶ S` to a separably closed extension `K`, the pullback exchange
`α : Lσ^* Ψ_M A ⟶ Ψ_{M_T} A` to the nearby cycles of the base change `M_T = M ×_S Spec K⟦t⟧`
(`NearbyCyclesModel.baseChange`) is an isomorphism if the restriction of `A` to the generic fibre
is bounded constructible. This is the case `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧` of
`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait`. -/
theorem isIso_pullbackExchange_baseChangeHom_traitMap
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) M.generic)
      (L((M.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A)) :
    IsIso (((baseChangeHom hM q (Category.comp_id q) (traitMap k' K)
      (Category.comp_id _)).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app A) := by
  have := hM.locallyOfFiniteType
  have := hM.quasiCompact
  have := hM.isSeparated
  have hT := IsTraitModelOver.baseChange hM q (Category.comp_id q) (traitMap k' K)
    (Category.comp_id _)
  exact Hom.isIso_pullbackExchange_app_of_isPullback_trait
    (PowerSeries.map_injective _ (algebraMap k' K).injective)
    (algebraMap_traitGenericField_injective k') (algebraMap_traitGenericField_injective K)
    (traitGenericFieldMap_comp_algebraMap k' K) PowerSeries.ker_coeff_eq_max_ideal
    PowerSeries.ker_coeff_eq_max_ideal _ q g hM.isPullback_j X'.hom hM.isPullback_i
    _ _ hT.isPullback_j _ hT.isPullback_i (IsPullback.of_hasPullback q (traitMap k' K))
    (baseChangeGenericMap_g hM q (Category.comp_id q) (traitMap k' K) (Category.comp_id _)) hA

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
