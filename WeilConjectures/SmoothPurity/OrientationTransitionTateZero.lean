/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.OrientationTransitionUnit
public import WeilConjectures.TateTwist.IntegralReduction

/-!
# The reduction of the integral Tate twist in degree zero

The integral Tate twist `𝒪_{E,Y}(0)`, placed in degree `0`, is the unit of `Dᵇc(Y)⟦𝒪_E⟧`
(`ProEtale.CondensedRing.integralTateTwistBoundedConstructibleNatZeroIso`). This file compares,
through it, the identification `red_m(𝒪_{E,Y}(0)) ≅ Λ_m(0)`
(`ProEtale.CondensedRing.etaleReductionIntegralTateTwistIso`) followed by `Λ_m(0) ≅ Λ_m` with the
reduction of the unit `red_m 𝒪 ≅ Λ_m` (`ProEtale.CondensedRing.etaleReductionUnitIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] [NeZero (ℓ : k)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The integral Tate twist `𝒪_{E,Y}(0)`, placed in degree `0`, is the unit of `Dᵇc(Y)⟦𝒪_E⟧`:
`𝒪_{E,Y}(0)` is the unit `𝒪_{E,Y}` by definition. -/
noncomputable def integralTateTwistBoundedConstructibleNatZeroIso :
    integralTateTwistBoundedConstructible ℓ E Y.hom 0 ≅ 𝟙_ _ :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (X := integralTateTwistBoundedConstructible ℓ E Y.hom 0) (Y := 𝟙_ _)
    (DerivedCategory.singleFunctorObjUnitIso (Mod (Sheaf (ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y.left)))

/-- **The reduction of the integral Tate twist in degree zero is the reduction of the unit**:
`red_m(𝒪_{E,Y}(0)) ≅ Λ_m(0) ≅ Λ_m` is `red_m` of `𝒪_{E,Y}(0) ≅ 𝒪`, followed by
`red_m 𝒪 ≅ Λ_m` (`etaleReductionUnitIso`). -/
lemma etaleReductionIntegralTateTwistIso_zero_hom_comp_twistObjectZeroIso_hom (m : ℕ)
    [NeZero (ringChar (integersModPowCoeff.{u} ℓ E m))]
    [HasInvertibleExponent (integersModPowCoeff.{u} ℓ E m) Y.left] :
    (etaleReductionIntegralTateTwistIso ℓ E m Y 0).hom ≫
        (Etale.HasTateTwist.twistObjectZeroIso (Λ := integersModPowCoeff.{u} ℓ E m) Y.left).hom =
      (etaleReduction ℓ E m Y).map (integralTateTwistBoundedConstructibleNatZeroIso ℓ E Y).hom ≫
        (etaleReductionUnitIso ℓ E m Y).hom := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
