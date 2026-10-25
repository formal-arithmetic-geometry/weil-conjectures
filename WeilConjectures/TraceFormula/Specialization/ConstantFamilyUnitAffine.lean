/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ConstantFamilyUnit

/-!

# The specialization unit of a weakly étale constant family

For a `k`-scheme `Y`, the constant family `Y × S` over the strictly henselian trait
`S = Spec k'⟦t⟧` is the deformation of the zero ideal of `Y`
(`ProEtale.CondensedRing.deformationModel Y ⊥ k'`). When the structure morphism `Y ⟶ Spec k` is
weakly étale (for instance `Y` étale over `k`, the spectrum of a finite separable `k`-algebra), the
projection `Y × S ⟶ S` is weakly étale, being a base change of `Y ⟶ Spec k`: the deformation space
`D_⊥ Y` is the relative affine line `𝔸¹_Y`
(`IdealSheafData.isIso_deformationSpaceToPolynomialSpec_bot`) and `𝔸¹_Y ⟶ 𝔸¹_k` is the base
change of `Y ⟶ Spec k` (`AffineSpace.isPullback_map`). Hence the pullback exchange of the
projection is invertible by weakly étale base change
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isPullback`), and the specialization unit of the
constant family is an isomorphism, for every commutative condensed ring `Λ` (blueprint
`det-sp-constant-family-vanishing`, the case of the unit for weakly étale `Y`).

## Main results

- `ProEtale.CondensedRing.weaklyEtale_deformationTotalToTrait_bot`: the projection `Y × S ⟶ S` is
  weakly étale when `Y ⟶ Spec k` is.
- `ProEtale.CondensedRing.isIso_deformationModel_bot_unit_of_weaklyEtale`: the specialization unit
  of the constant family of a weakly étale `k`-scheme is an isomorphism.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] (Y : Over (Spec (.of k))) (k' : Type u) [Field k'] [Algebra k k']

/-- The coordinate `t : D_⊥ Y = 𝔸¹_Y ⟶ 𝔸¹_k` of the deformation space of the zero ideal is weakly
étale when `Y ⟶ Spec k` is: it is a base change of `Y ⟶ Spec k`. -/
instance weaklyEtale_deformationSpaceToAffineLine_bot [WeaklyEtale Y.hom] :
    WeaklyEtale (deformationSpaceToAffineLine Y ⊥) := by
  have : WeaklyEtale (AffineSpace.map (ULift.{u} (Fin 1)) Y.hom) :=
    MorphismProperty.of_isPullback (AffineSpace.isPullback_map Y.hom).flip ‹_›
  unfold deformationSpaceToAffineLine
  infer_instance

/-- The projection `Y × S ⟶ S` of the constant family is weakly étale when `Y ⟶ Spec k` is. -/
instance weaklyEtale_deformationTotalToTrait_bot [WeaklyEtale Y.hom] :
    WeaklyEtale (deformationTotalToTrait Y ⊥ k') :=
  inferInstanceAs (WeaklyEtale (pullback.snd _ _))

/-- **The constant family of a weakly étale `k`-scheme** (blueprint
`det-sp-constant-family-vanishing`, the case of the unit for weakly étale `Y`): if the structure
morphism `Y ⟶ Spec k` is weakly étale, the specialization unit of the constant family `Y × S` is
an isomorphism, for every commutative condensed ring `Λ`. The projection `Y × S ⟶ S` is weakly
étale and its geometric generic fibre is a base change, so its pullback exchange is invertible
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isPullback`). -/
theorem isIso_deformationModel_bot_unit_of_weaklyEtale [IsSepClosed k'] [WeaklyEtale Y.hom] :
    IsIso ((deformationModel Y ⊥ k').unit Λ) := by
  have : WeaklyEtale (constantFamilyModelHom Y k').total :=
    inferInstanceAs (WeaklyEtale (deformationTotalToTrait Y ⊥ k'))
  have : WeaklyEtale (constantFamilyModelHom Y k').generic :=
    inferInstanceAs (WeaklyEtale (pullback.snd _ _))
  have : IsIso ((constantFamilyModelHom Y k').pullbackExchange Λ) :=
    (constantFamilyModelHom Y k').isIso_pullbackExchange_of_isPullback Λ
      (IsPullback.of_hasPullback _ _).flip
  exact isIso_deformationModel_bot_unit_of_isIso_pullbackExchange_app Λ Y k'

end AlgebraicGeometry.ProEtale.CondensedRing
