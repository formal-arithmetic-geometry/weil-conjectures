/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ComponentSpecialFibre
public import WeilConjectures.TraceFormula.Specialization.PointExchangeOnComponent

/-!

# The exchange `ν_X` on pushforwards, for an abstract `ν` and on thickened points

`pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_of_eq` is the identity of
`pointCompactSupportExchangeOfOpenImmersion_app_lowerStar` for any `ν` equal to
`pointCompactSupportExchangeOfOpenImmersion x u k'` (`hν`), with all the shape data of
`openPointExchangeAux_app_comp_aux_of_eq` given explicitly (as in `ExchangeOnProperBdc`). It is
instantiated

* for the morphism of deformation models `pointComponentModelHom` over `g : B ⟶ X` with
  `b ≫ g = x` (the thickened point `B` of a fixed locus,
  `pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_component`);
* for `ν_X = pointCompactSupportExchangeOfSeparated` (by `rfl`,
  `pointCompactSupportExchangeOfSeparated_app_lowerStar` and `…_component`).

## Implementation notes

The ambient hypothesis `hC` is still a hypothesis. With the data given explicitly, its type and
that of `NearbyCyclesModel.Hom.compactSupportExchange_comp_app` (instantiated at `Λ = ℚ̄_ℓ`, with
the object `ι N` written as `@Functor.obj Dᵇc(B)⟦Λ⟧ _ _ _ ι N`) differ only in proof subterms:
the instance `Precoherent Profinite` occurs as `ProEtale.pointLowerStar._proof_1` in the instance
terms coming from `Profinite.padicAlgClRingObj ℓ` and as the synthesized instance in those coming
from the generic `Λ`. Both the elaborator and the kernel unfold the instances (e.g. the monoidal
structure on condensed abelian groups) instead of using proof irrelevance, and time out (the kernel
runs out of memory at `maxHeartbeats 3000000`), also when the identification is made by a
congruence on the differing proofs.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Point

set_option hygiene false in
/-- The coefficients `ℚ̄_ℓ`. -/
local notation "Λℓ" => Profinite.padicAlgClRingObj ℓ

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))} (x : RationalPoint X) (u : X ⟶ Y)
  [IsOpenImmersion u.left] (k' : Type u) [Field k'] [Algebra k k']

instance isOpenImmersion_pointModelHom_total : IsOpenImmersion (pointModelHom x u k').total :=
  isOpenImmersion_deformationTotalMap u _ k' (ker_eq_comap_of_isOpenImmersion x u)

/-- The structure map of a proper `k`-scheme is proper. -/
lemma isProper_toPoint_left_of_isProper (Z : Over (Spec (.of k))) [IsProper Z.hom] :
    IsProper (toPoint Z).left :=
  ‹IsProper Z.hom›

attribute [local instance] isProper_toPoint_left_of_isProper

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The nearby cycles of the deformation to the normal cone preserve `Dᵇc`. -/
lemma preservesBoundedConstructible_deformationModel (Z : Over (Spec (.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (z : RationalPoint Z) :
    (deformationModel Z z.left.ker k').PreservesBoundedConstructible Λℓ :=
  (deformationModel Z z.left.ker k').preservesBoundedConstructible_of_isTraitModel (ℓ := ℓ)
    (isTraitModel_deformationModel Z _ k') (deformationModel_exists_comp_ε Z _ k')

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The nearby cycles of the trait preserve `Dᵇc`. -/
lemma preservesBoundedConstructible_traitModel :
    (traitModel k k').PreservesBoundedConstructible Λℓ :=
  (traitModel k k').preservesBoundedConstructible_of_isTraitModel (ℓ := ℓ)
    (isTraitModel_traitModel k k') ⟨traitToBase k k', traitModel_j_traitToBase k k'⟩

set_option hygiene false in
/-- `Dᵇc` is preserved by the nearby cycles of the deformation of `X` along `x`. -/
local notation "hPX" => preservesBoundedConstructible_deformationModel (ℓ := ℓ) k' X x

set_option hygiene false in
/-- `Dᵇc` is preserved by the nearby cycles of the deformation of `Y` along `x ≫ u`. -/
local notation "hPY" => preservesBoundedConstructible_deformationModel (ℓ := ℓ) k' Y (x ≫ u)

variable [IsProper Y.hom] {B : Over (Spec (.of k))} {B' : Scheme.{u}}
  {MB : NearbyCyclesModel B.left B'} {g : B ⟶ X}
  {g' : B' ⟶ (deformationSpecialFibre X x.left.ker k').left}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType B.hom]
  [QuasiCompact B.hom] [IsSeparated B.hom]
  (φg : MB.Hom (deformationModel X x.left.ker k') g.left g')

/-- **The exchange `ν_X` on pushforwards from `B`, for `ν = ν_X`**: the identity of
`pointCompactSupportExchangeOfOpenImmersion_app_lowerStar` for any `ν` equal to
`pointCompactSupportExchangeOfOpenImmersion x u k'`, the shape data of
`openPointExchangeAux_app_comp_aux_of_eq` being those of the definition of `ν_X`, given
explicitly. -/
theorem pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_of_eq
    (ν : Correspondence.IsContractingAt.PointCompactSupportExchange (ℓ := ℓ) X k' x)
    (hν : ν = pointCompactSupportExchangeOfOpenImmersion x u k') (N : Dᵇc(B.left)⟦Λℓ⟧) :
    ∀ hC, type_of% (
      openPointExchangeAux_app_comp_aux_of_eq
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λℓ ℓ u)
      (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λℓ ℓ
        (pointSpecialMap x u k'))
      ((pointModelHom x u k').boundedConstructiblePullbackExchange ℓ hPX hPY)
      ((pointModelHom x u k').isIso_boundedConstructiblePullbackExchange_of_isOpenImmersion ℓ
        hPX hPY (isPullback_deformationGenericMap u (ker_compatible_of_isOpenImmersion x u) k'))
      (lowerShriekCompOfEq ℓ (pointSpecialMap x u k') (toPoint _) (comp_toPoint _) ≪≫
        Functor.isoWhiskerRight
          (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
            (pointSpecialMap x u k')) _)
      (lowerShriekCompOfEq ℓ u (toPoint Y) (comp_toPoint u) ≪≫ Functor.isoWhiskerRight
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ u) _)
      (ObjectProperty.fullyFaithfulι (boundedConstructible (condensedRingObj Λℓ (point k').left)))
      (ObjectProperty.fullyFaithfulι (boundedConstructible (condensedRingObj Λℓ Y.left)))
      (lowerShriekCompOfEq ℓ (deformationSpecialFibreToCompactified Y (x ≫ u) k')
        (toPoint _) (comp_toPoint _))
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
        (deformationSpecialFibreToCompactified Y (x ≫ u) k'))
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
        (toPoint (compactifiedSpecialFibre Y (x ≫ u) k')))
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y))
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hPY)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ
        (deformationSpecialFibreToCompactified Y (x ≫ u) k'))
      (boundedConstructibleLowerStarCompatibility Λℓ ℓ
        (toPoint (compactifiedSpecialFibre Y (x ≫ u) k')))
      (boundedConstructibleLowerStarCompatibility Λℓ ℓ (toPoint Y))
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility
        (preservesBoundedConstructible_traitModel (k := k) (ℓ := ℓ) k'))
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λℓ
        (deformationSpecialFibreToCompactified Y (x ≫ u) k').left).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λℓ _).symm)
      (leftDerivedUpperStarId Λℓ Y.left).symm
      ((deformationToCompactifiedModelHom Y (x ≫ u) k').pullbackExchange Λℓ)
      (isIso_deformationToCompactifiedModelHom_pullbackExchange Y (x ≫ u) k')
      ((compactifiedToPointModelHom Y (x ≫ u) k').pushforwardExchange Λℓ)
      (isIsoOn_compactifiedToPointModelHom_pushforwardExchange Y (x ≫ u) k') ν hν
      (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hPX)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ u)
      (boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ (pointSpecialMap x u k'))
      (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ u.left)
        (openImmersionAdjunction ℓ (pointSpecialMap x u k').left)
        ((pointModelHom x u k').pullbackExchange Λℓ))
      (fun K ↦ map_mateEquiv_inv_liftExchange _ _ _ _ _ _ _ _ _ _ K)
      (boundedConstructibleLowerStarCompatibility Λℓ ℓ g)
      (closedExtension (openImmersionAdjunction ℓ u.left) (rfl : g.left ≫ u.left = _))
      (closedExtension (Adjunction.id.ofNatIsoRight (leftDerivedUpperStarId Λℓ Y.left).symm)
        (rfl : (g.left ≫ u.left) ≫ 𝟙 Y.left = _))
      (lowerStarCompOfEq (rfl : ((g.left ≫ u.left) ≫ 𝟙 Y.left) ≫ (toPoint Y).left = _))
      (φg.pushforwardExchange Λℓ)
      (closedExtension (openImmersionAdjunction ℓ (pointSpecialMap x u k').left)
        (rfl : g' ≫ (pointSpecialMap x u k').left = _))
      (closedExtension (openImmersionAdjunction ℓ
        (deformationSpecialFibreToCompactified Y (x ≫ u) k').left) rfl)
      (lowerStarCompOfEq rfl)
      ((pointCompModelHom x u k' φg).pushforwardExchange Λℓ) N
      ⟨_, boundedConstructible_rightDerivedLowerStar_obj Λℓ ℓ (g ≫ u) N.obj N.property⟩
      (Iso.refl _) hC) :=
  fun hC ↦ openPointExchangeAux_app_comp_aux_of_eq
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λℓ ℓ u)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λℓ ℓ
      (pointSpecialMap x u k'))
    ((pointModelHom x u k').boundedConstructiblePullbackExchange ℓ hPX hPY)
    ((pointModelHom x u k').isIso_boundedConstructiblePullbackExchange_of_isOpenImmersion ℓ
      hPX hPY (isPullback_deformationGenericMap u (ker_compatible_of_isOpenImmersion x u) k'))
    (lowerShriekCompOfEq ℓ (pointSpecialMap x u k') (toPoint _) (comp_toPoint _) ≪≫
      Functor.isoWhiskerRight
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
          (pointSpecialMap x u k')) _)
    (lowerShriekCompOfEq ℓ u (toPoint Y) (comp_toPoint u) ≪≫ Functor.isoWhiskerRight
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ u) _)
    (ObjectProperty.fullyFaithfulι (boundedConstructible (condensedRingObj Λℓ (point k').left)))
    (ObjectProperty.fullyFaithfulι (boundedConstructible (condensedRingObj Λℓ Y.left)))
    (lowerShriekCompOfEq ℓ (deformationSpecialFibreToCompactified Y (x ≫ u) k')
      (toPoint _) (comp_toPoint _))
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ
      (deformationSpecialFibreToCompactified Y (x ≫ u) k'))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ
      (toPoint (compactifiedSpecialFibre Y (x ≫ u) k')))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y))
    (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hPY)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ
      (deformationSpecialFibreToCompactified Y (x ≫ u) k'))
    (boundedConstructibleLowerStarCompatibility Λℓ ℓ
      (toPoint (compactifiedSpecialFibre Y (x ≫ u) k')))
    (boundedConstructibleLowerStarCompatibility Λℓ ℓ (toPoint Y))
    (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility
      (preservesBoundedConstructible_traitModel (k := k) (ℓ := ℓ) k'))
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λℓ
      (deformationSpecialFibreToCompactified Y (x ≫ u) k').left).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λℓ _).symm)
    (leftDerivedUpperStarId Λℓ Y.left).symm
    ((deformationToCompactifiedModelHom Y (x ≫ u) k').pullbackExchange Λℓ)
    (isIso_deformationToCompactifiedModelHom_pullbackExchange Y (x ≫ u) k')
    ((compactifiedToPointModelHom Y (x ≫ u) k').pushforwardExchange Λℓ)
    (isIsoOn_compactifiedToPointModelHom_pushforwardExchange Y (x ≫ u) k') ν hν
    (NearbyCyclesModel.boundedConstructibleNearbyCyclesCompatibility hPX)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ u)
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λℓ ℓ (pointSpecialMap x u k'))
    (lowerShriekExchangeOfInv (openImmersionAdjunction ℓ u.left)
      (openImmersionAdjunction ℓ (pointSpecialMap x u k').left)
      ((pointModelHom x u k').pullbackExchange Λℓ))
    (fun K ↦ map_mateEquiv_inv_liftExchange _ _ _ _ _ _ _ _ _ _ K)
    (boundedConstructibleLowerStarCompatibility Λℓ ℓ g)
    (closedExtension (openImmersionAdjunction ℓ u.left) (rfl : g.left ≫ u.left = _))
    (closedExtension (Adjunction.id.ofNatIsoRight (leftDerivedUpperStarId Λℓ Y.left).symm)
      (rfl : (g.left ≫ u.left) ≫ 𝟙 Y.left = _))
    (lowerStarCompOfEq (rfl : ((g.left ≫ u.left) ≫ 𝟙 Y.left) ≫ (toPoint Y).left = _))
    (φg.pushforwardExchange Λℓ)
    (closedExtension (openImmersionAdjunction ℓ (pointSpecialMap x u k').left)
      (rfl : g' ≫ (pointSpecialMap x u k').left = _))
    (closedExtension (openImmersionAdjunction ℓ
      (deformationSpecialFibreToCompactified Y (x ≫ u) k').left) rfl)
    (lowerStarCompOfEq rfl)
    ((pointCompModelHom x u k' φg).pushforwardExchange Λℓ) N
    ⟨_, boundedConstructible_rightDerivedLowerStar_obj Λℓ ℓ (g ≫ u) N.obj N.property⟩
    (Iso.refl _) hC

end Point

section Component

variable {k : Type u} [Field k] {X B : Over (Spec (.of k))} {x : RationalPoint X}
  {b : RationalPoint B} (k' : Type u) [Field k'] [Algebra k k'] (g : B ⟶ X) (hbg : b ≫ g = x)

/-- The morphism of deformation models `𝒟_B ⟶ 𝒳` over `g : B ⟶ X` with `b ≫ g = x`, for the
deformations of `B` along `ker b` and of `X` along `ker x`. -/
noncomputable abbrev pointComponentModelHom :=
  deformationModelHom g (map_siteIdeal_ker_le_of_comp_eq g hbg) k'

variable {Y : Over (Spec (.of k))} (u : X ⟶ Y) [IsOpenImmersion u.left] [IsProper Y.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]

/-- **The exchange `ν_X` on pushforwards from a thickened point `B`** (`b ≫ g = x`):
`pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_of_eq` for `pointComponentModelHom`. -/
theorem pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_component
    (ν : Correspondence.IsContractingAt.PointCompactSupportExchange (ℓ := ℓ) X k' x)
    (hν : ν = pointCompactSupportExchangeOfOpenImmersion x u k')
    (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    type_of% (pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_of_eq x u k'
      (pointComponentModelHom k' g hbg) ν hν N) :=
  pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_of_eq x u k' _ ν hν N

end Component

section Separated

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

instance isProper_compactificationOverField_overObj :
    IsProper (compactificationOverField (toPoint X)).overObj.hom :=
  have := (compactificationOverField (toPoint X)).isProper
  inferInstanceAs (IsProper (_ ≫ 𝟙 _))

variable (x : RationalPoint X) (k' : Type u) [Field k'] [Algebra k k'] {ℓ : ℕ} [Fact ℓ.Prime]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] {B : Over (Spec (.of k))} [LocallyOfFiniteType B.hom]
  [QuasiCompact B.hom] [IsSeparated B.hom]

/-- **The exchange `ν_X` of a separated `X` on pushforwards from `B`**:
`pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_of_eq` for the compactification
`X ⊂ X̄` of `a_X` and `ν = pointCompactSupportExchangeOfSeparated` (`rfl`). -/
theorem pointCompactSupportExchangeOfSeparated_app_lowerStar {B' : Scheme.{u}}
    {MB : NearbyCyclesModel B.left B'} {g : B ⟶ X}
    {g' : B' ⟶ (deformationSpecialFibre X x.left.ker k').left}
    (φg : MB.Hom (deformationModel X x.left.ker k') g.left g')
    (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    type_of% (pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_of_eq x
      (compactificationOverField (toPoint X)).overI k' φg
      (pointCompactSupportExchangeOfSeparated x k') rfl N) :=
  pointCompactSupportExchangeOfOpenImmersion_app_lowerStar_of_eq x _ k' φg _ rfl N

/-- **The exchange `ν_X` of a separated `X` on pushforwards from a thickened point `B`**
(`b ≫ g = x`): `pointCompactSupportExchangeOfSeparated_app_lowerStar` for
`pointComponentModelHom`. -/
theorem pointCompactSupportExchangeOfSeparated_app_lowerStar_component {b : RationalPoint B}
    (g : B ⟶ X) (hbg : b ≫ g = x) (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    type_of% (pointCompactSupportExchangeOfSeparated_app_lowerStar x k'
      (pointComponentModelHom k' g hbg) N) :=
  pointCompactSupportExchangeOfSeparated_app_lowerStar x k' _ N

end Separated

end AlgebraicGeometry.ProEtale.CondensedRing
