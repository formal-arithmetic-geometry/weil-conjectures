/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Exchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperComplete
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedUpperStarProducts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedAdicCompleteConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeAmbient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionLowerStarEtaleOrigin
public import WeilConjectures.TraceFormula.Specialization.TraitModelRestrict
public import WeilConjectures.Tactic.ExactModProofs

/-!

# Proper base change along the special fibre at generic direct images

Let `φ : M ⟶ N` be a morphism of nearby-cycles models of finite type over the trait
`S = Spec k'⟦t⟧` (`NearbyCyclesModel.IsTraitModel`) whose morphism of total spaces `t` is proper
and whose square of special fibres is cartesian. For a bounded constructible `ℚ̄_ℓ`-complex `L`
on the geometric generic fibre of `M`, the base change morphism
`Li_N^* Rt_* ⟶ Rt_{s*} Li_M^*` is invertible at the generic direct image `Rj_{M*} L`
(`NearbyCyclesModel.Hom.isIso_baseChangeMap_commSq_i_app_lowerStar`). This is the step
`ī^* Rt̄_* ≃ Rt_{s*} ī'^*` of the proof of blueprint `det-sp-nearby-cycles-exchanges` (2).

The complex `Rj_{M*} L` is not bounded constructible, so the proper base change theorem for
bounded constructible complexes does not apply. The proof passes to an integral model `L₀` of
`L` (`ProEtale.exists_padicAlgCl_iso_integralModel`): `L₀` is derived `ℓ`-adically complete
(`ProEtale.isDerivedAdicComplete_of_boundedConstructible`), hence so is `Rj_{M*} L₀`, and the
first derived reduction of `Rj_{M*} L₀` is the direct image of a complex of étale origin, so of
étale origin. Proper base change for such complexes
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_isProper_of_isDerivedAdicComplete`), along
the special fibres, whose pullbacks preserve countable products
(`ProEtale.CondensedRing.preservesLimitsOfShape_leftDerivedUpperStar_of_isClosedImmersion`),
gives the integral statement, and the coefficient changes `𝒪_E → E → ℚ̄_ℓ` commute with the
direct images of bounded below complexes and with base change morphisms.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] {X : Scheme.{u}} {X' : Over (Spec (.of k'))}

variable {ℓ : ℕ} [Fact ℓ.Prime]

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
