/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.CategoryTheory.Idempotents.Triangulated
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.KaroubianSubcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Retract
public import WeilConjectures.SixFunctors.ClosedImmersionStages
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.SixFunctors.ProEtale.Adic.Abelian
public import WeilConjectures.SixFunctors.ProEtale.Adic.Extension

/-!
# Idempotent completeness of the rational and `ℚ̄_ℓ` stages

Blueprint `lem-weil-rationalization-idempotent-complete` and
`lem-weil-qbar-idempotent-complete`: the categories `Dᵇc(Y, E)` and `Dᵇc(Y, ℚ̄_ℓ)` are idempotent
complete, and their inclusions into their Karoubi envelopes are exact equivalences.

* The rational stage `Dᵇc(Y, E)`
  (`AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructibleRational`) is by definition the
  Karoubi envelope of the rationalization of `Dᵇc(Y, 𝒪_E)`, hence idempotent complete. The
  rationalization of `Dᵇc(Y, 𝒪_E)` is stable under the shifts of `D_comp(Y_ét, E)`, so
  `Dᵇc(Y, E)` has a shift and the inclusion into its Karoubi envelope commutes with it.
* The stage `Dᵇc(Y, ℚ̄_ℓ)` (`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleAdic`)
  consists of bounded objects of the derived category of `ℓ`-adic sheaves, whose idempotents
  split (`CategoryTheory.Triangulated.TStructure.isSplit_of_bounded`), and it is closed under
  retracts on a locally noetherian scheme, constructible sheaves being closed under kernels
  there. It is a triangulated subcategory, so that the inclusion into its Karoubi envelope is
  a triangulated equivalence.

## Limitations

* At the rational stage the repository does not (yet) provide a triangulated structure on the
  rationalization of `Dᵇc(Y, 𝒪_E)`: this would need `Dᵇc(Y, 𝒪_E)` to be closed under
  extensions, hence the constructible sheaves of `𝒪_E`-modules to be closed under extensions,
  which is only available for finite coefficient rings
  (`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_shortExact`). We prove the compatibility of
  `Dᵇc(Y, E) ⥤ Kar(Dᵇc(Y, E))` with the shifts, and its triangulatedness under the assumption
  that the rationalization of `Dᵇc(Y, 𝒪_E)` is a triangulated subcategory of `D_comp(Y_ét, E)`.
* At the stage `ℚ̄_ℓ` the scheme is assumed locally noetherian, where the closure of
  constructible sheaves under kernels, hence retracts, and the triangulated structure of
  `Dᵇc(Y, ℚ̄_ℓ)` are available.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Idempotents

namespace AlgebraicGeometry

open Scheme

section Rational

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

omit [Fact l.Prime] [Field E] [Algebra E (PadicAlgCl l)] [Small.{u + 1} E] [Algebra ℚ_[l] E]
  [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] in
/-- The integral stage `Dᵇc(X, Λ)` is stable under shifts: if `K` lies in it, so does every
derived complete object isomorphic to a shift `K⟦n⟧`, the reductions of `K⟦n⟧` being the shifts
of those of `K`. -/
lemma Etale.DerivedCategory.boundedConstructibleIntegral_of_iso_shift {Λ : Type (u + 1)}
    [CommRing Λ] (I : Ideal Λ) {X : Scheme.{u}}
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.boundedConstructibleIntegral I X K) (n : ℤ) (e : K⟦n⟧ ≅ L)
    (hL : DerivedCategory.derivedComplete X.smallEtaleTopology I L) :
    Etale.DerivedCategory.boundedConstructibleIntegral I X L := by
  obtain ⟨-, a, b, h⟩ := hK
  refine ⟨hL, a - n, b - n, fun m ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := h m
  let e' : (reductionModIdeal Λ X (I ^ (m + 1))).obj L ≅
      ((reductionModIdeal Λ X (I ^ (m + 1))).obj K)⟦n⟧ :=
    (reductionModIdeal Λ X (I ^ (m + 1))).mapIso e.symm ≪≫
      ((reductionModIdeal Λ X (I ^ (m + 1))).commShiftIso n).app K
  exact ⟨(Etale.DerivedCategory.boundedConstructible _ X).prop_of_iso e'.symm
      ((Etale.DerivedCategory.boundedConstructible _ X).le_shift n _ h₁),
    (Etale.DerivedCategory.torAmplitudeIn _ X _ _).prop_of_iso e'.symm
      (Etale.DerivedCategory.torAmplitudeIn.shift h₂ n)⟩

/-- The rationalization of `Dᵇc(X, 𝒪_E)` is stable under the shifts of `D_comp(X_ét, E)`: the
shift of the image of `L ∈ Dᵇc(X, 𝒪_E)` is the image of `L⟦n⟧ ∈ Dᵇc(X, 𝒪_E)`. -/
theorem Etale.DerivedCategory.boundedConstructibleRational_shift {X : Scheme.{u}}
    {K : DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E}
    (hK : Etale.DerivedCategory.boundedConstructibleRational l E X K) (n : ℤ) :
    Etale.DerivedCategory.boundedConstructibleRational l E X (K⟦n⟧) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := hK
  exact ⟨L⟦n⟧, Etale.DerivedCategory.boundedConstructibleIntegral_of_iso_shift _ hL n
    (((DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).ι.commShiftIso
      n).app L).symm (L⟦n⟧).property,
    ⟨((DerivedCategoryDerivedCompleteRational.fromIntegral _ l E).commShiftIso n).app L ≪≫
      (shiftFunctor _ n).mapIso e⟩⟩

instance Etale.DerivedCategory.isStableUnderShift_boundedConstructibleRational
    (X : Scheme.{u}) :
    (Etale.DerivedCategory.boundedConstructibleRational l E X).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    ⟨fun _ hK ↦ Etale.DerivedCategory.boundedConstructibleRational_shift l E hK n⟩

variable (Y : Scheme.{u})

/-- Blueprint `lem-weil-rationalization-idempotent-complete`: the rational stage `Dᵇc(Y, E)`,
the Karoubi envelope of the rationalization of `Dᵇc(Y, 𝒪_E)`, is idempotent complete. -/
instance Etale.isIdempotentComplete_derivedCategoryBoundedConstructibleRational :
    IsIdempotentComplete (Etale.DerivedCategoryBoundedConstructibleRational l E Y) :=
  inferInstance

/-- Blueprint `lem-weil-rationalization-idempotent-complete`: the canonical functor
`Dᵇc(Y, E) ⥤ Kar(Dᵇc(Y, E))` into the Karoubi envelope is an equivalence. -/
instance Etale.isEquivalence_toKaroubi_derivedCategoryBoundedConstructibleRational :
    (toKaroubi (Etale.DerivedCategoryBoundedConstructibleRational l E Y)).IsEquivalence :=
  inferInstance

/-- Blueprint `lem-weil-rationalization-idempotent-complete`: the canonical functor
`Dᵇc(Y, E) ⥤ Kar(Dᵇc(Y, E))` commutes with the shifts, the shift of `Dᵇc(Y, E)` being the
extension to the Karoubi envelope of the shift of the rationalization of `Dᵇc(Y, 𝒪_E)`. -/
noncomputable instance Etale.commShift_toKaroubi_derivedCategoryBoundedConstructibleRational :
    (toKaroubi (Etale.DerivedCategoryBoundedConstructibleRational l E Y)).CommShift ℤ :=
  inferInstance

/-- Blueprint `lem-weil-rationalization-idempotent-complete`: if the rationalization of
`Dᵇc(Y, 𝒪_E)` is a triangulated subcategory of `D_comp(Y_ét, E)`, then the canonical
equivalence `Dᵇc(Y, E) ⥤ Kar(Dᵇc(Y, E))` is a triangulated functor, for the triangulated
structures on Karoubi envelopes of `CategoryTheory.Idempotents.Karoubi.pretriangulated`. -/
theorem Etale.isTriangulated_toKaroubi_derivedCategoryBoundedConstructibleRational
    [(Etale.DerivedCategory.boundedConstructibleRational l E Y).IsTriangulated] :
    (toKaroubi (Etale.DerivedCategoryBoundedConstructibleRational l E Y)).IsTriangulated :=
  inferInstance

end Rational

section AlgebraicClosure

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) [IsLocallyNoetherian Y]

/-- On a locally noetherian scheme, constructible `ℓ`-adic sheaves are stable under retracts,
being closed under kernels. -/
instance ProEtale.isStableUnderRetracts_adicConstructibleSheaf :
    (ProEtale.adicConstructibleSheaf l Y).IsStableUnderRetracts :=
  ObjectProperty.isStableUnderRetracts_of_isClosedUnderKernels _

/-- On a locally noetherian scheme, `Dᵇc(Y, ℚ̄_ℓ)` is stable under retracts: the homology
sheaves of a retract are retracts of constructible sheaves. -/
instance ProEtale.isStableUnderRetracts_boundedConstructibleAdic :
    (ProEtale.DerivedCategory.boundedConstructibleAdic l Y).IsStableUnderRetracts where
  of_retract e h := ⟨_root_.DerivedCategory.TStructure.t.bounded.prop_of_retract e h.1,
    (_root_.DerivedCategory.homologyProperty _).prop_of_retract e h.2⟩

/-- Blueprint `lem-weil-qbar-idempotent-complete`: `C_Y = Dᵇc(Y, ℚ̄_ℓ)` is idempotent complete.
Its objects are bounded, so their idempotents split in the derived category of `ℓ`-adic sheaves
(`CategoryTheory.Triangulated.TStructure.isSplit_of_bounded`), through retracts which again lie
in `Dᵇc(Y, ℚ̄_ℓ)`. -/
instance ProEtale.isIdempotentComplete_boundedConstructibleAdic :
    IsIdempotentComplete (ProEtale.DerivedCategory.boundedConstructibleAdic l Y).FullSubcategory :=
  _root_.DerivedCategory.TStructure.t.isIdempotentComplete_fullSubcategory_of_le_bounded _
    fun _ h ↦ h.1

/-- Blueprint `lem-weil-qbar-idempotent-complete`: the canonical functor
`Dᵇc(Y, ℚ̄_ℓ) ⥤ Kar(Dᵇc(Y, ℚ̄_ℓ))` into the Karoubi envelope is an equivalence. -/
instance ProEtale.isEquivalence_toKaroubi_boundedConstructibleAdic :
    (toKaroubi
      (ProEtale.DerivedCategory.boundedConstructibleAdic l Y).FullSubcategory).IsEquivalence :=
  inferInstance

/-- Blueprint `lem-weil-qbar-idempotent-complete`: the canonical equivalence
`Dᵇc(Y, ℚ̄_ℓ) ⥤ Kar(Dᵇc(Y, ℚ̄_ℓ))` is a triangulated functor. Here `Dᵇc(Y, ℚ̄_ℓ)` is a
triangulated subcategory of the derived category of `ℓ`-adic sheaves, constructible sheaves
being closed under kernels, cokernels and extensions. -/
instance ProEtale.isTriangulated_toKaroubi_boundedConstructibleAdic :
    (toKaroubi
      (ProEtale.DerivedCategory.boundedConstructibleAdic l Y).FullSubcategory).IsTriangulated :=
  inferInstance

end AlgebraicClosure

end AlgebraicGeometry
