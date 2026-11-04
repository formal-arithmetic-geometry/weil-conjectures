/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseExtensionConstructible
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality

/-! Constructibility of a single integral locally closed extension in the topological
Noetherian setting. Source: Bhatt--Scholze, Lemma 6.8.13, and step 1 of the plan of
lem-sfb-topological-integral-generators
(blueprint: lem-sfb-topological-integral-extension-constructibility).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A locally finite free module object over `Λ_X` is lisse: on each member of the
trivializing cover, the pullback over the pulled-back ring `g^* Λ_X` is free, and the
coefficient comparison `g^* Λ_X ≅ Λ_W` transports freeness to the canonical pullback.
Source: Bhatt--Scholze, Section 6.8; Stacks Project, Tag 03DO
(blueprint: lem-sfb-topological-integral-extension-constructibility). -/
theorem CondensedRing.LocallyFree.isLisseCoefficientModule
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (hM : CondensedRing.LocallyFree (condensedRingObj Λ X) M) :
    IsLisseCoefficientModule Λ M := by
  obtain ⟨C, hC⟩ := hM
  exact ⟨C, fun s ↦ ProEtale.free_of_iso
    (ProEtale.free_comap (inv (condensedPullbackHom Λ (C.f s))) (hC s))
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ (C.f s))).app _).symm⟩

/-- The extension by zero `i_* j_! L` of a lisse module object along an open immersion
`j : T ⟶ Z` followed by a closed immersion `i : Z ⟶ X` into a topologically Noetherian
scheme is constant-model constructible, for any commutative condensed ring `Λ`: its
restrictions to the strata `T`, `Z ∖ T` and `X ∖ Z` are `L`, `0` and `0`.
Source: Bhatt--Scholze, Lemma 6.8.13; definition sk-def-sfb-constructible
(blueprint: lem-sfb-topological-integral-extension-constructibility). -/
theorem isConstantModelConstructible_lowerStar_openImmersionLowerShriek_obj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X T Z : Scheme.{u}} [TopologicalSpace.NoetherianSpace X] (j : T ⟶ Z) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i]
    (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hL : IsLisseCoefficientModule Λ L) :
    IsConstantModelConstructible Λ X
      ((CondensedRing.lowerStar Λ i).obj
        ((CondensedRing.openImmersionLowerShriek Λ j).obj L)) := by
  have : TopologicalSpace.NoetherianSpace Z := i.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := ⟨fun _ _ _ ↦
    j.isOpenEmbedding.isEmbedding.isCompact_iff.2 (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  obtain ⟨R, hR⟩ := stratified_openExtension Λ j L
    (stratified_of_finiteModel Λ T L (lisse_finiteModel Λ T L hL))
  let U := Scheme.openComplementOfIsClosedImmersion i
  have hU : Set.range U.ι = (Set.range i)ᶜ := by
    simp [U, Scheme.openComplementOfIsClosedImmersion]
  have : QuasiCompact U.ι := ⟨fun _ _ _ ↦ U.ι.isOpenEmbedding.isEmbedding.isCompact_iff.2
    (TopologicalSpace.NoetherianSpace.isCompact _)⟩
  have := CondensedRing.moduleCounitOfAbelian Λ i
    (ProEtale.isIso_upperStarLowerStarAdjunction_counit Ab.{u + 1} i)
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  refine stratified_of_restrictions Λ U.ι i (by rw [hU, compl_compl]) _ ?_ ⟨R, fun a ↦ ?_⟩
  · exact finiteConstantStratified_of_isZero Λ _ _
      (CondensedRing.openRestrictionPushforwardZero Λ i U.ι hU _)
  · exact finiteModel_iso Λ _ ((CondensedRing.upperStar Λ (R.immersion a)).mapIso
      (asIso ((CondensedRing.upperStarLowerStarAdjunction Λ i).counit.app _)).symm) (hR a)

end AlgebraicGeometry.ProEtale

namespace WeilConjectures.SixFunctors

/-- `isConstantModelConstructible_lowerStar_openImmersionLowerShriek_obj` for a ring object
`Λ`, stated with the coefficient ring `(coefficientRing T Λ).X` and `integralLowerShriek`:
for a locally finite free `L` the extension by zero `i_* j_! L` is constant-model
constructible. Stating it for an abstract `Λ` keeps the kernel from unfolding concrete
coefficient rings.
Source: Bhatt--Scholze, Lemma 6.8.13
(blueprint: lem-sfb-topological-integral-extension-constructibility). -/
theorem isConstantModelConstructible_integralLowerShriek
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) [IsCommMonObj Λ.X]
    {X T Z : Scheme.{u}} [TopologicalSpace.NoetherianSpace X] (j : T ⟶ Z) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i]
    (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (coefficientRing T Λ).X)
    (hL : CondensedRing.LocallyFree (coefficientRing T Λ).X L) :
    IsConstantModelConstructible Λ.X X (integralLowerShriek X Λ.X j i L) :=
  isConstantModelConstructible_lowerStar_openImmersionLowerShriek_obj Λ.X j i L
    (CondensedRing.LocallyFree.isLisseCoefficientModule Λ.X hL)

/-- The integral extension by zero `i_* j_! L₀` of a locally finite free `O_E`-module is
constant-model constructible on a topologically Noetherian scheme.

Source: step 1 of the plan of lem-sfb-topological-integral-generators; definition
sk-def-sfb-constructible (blueprint: lem-sfb-topological-integral-extension-constructibility).

Proof:
1. `X` is topologically Noetherian, so it is quasi-compact and quasi-separated and every
   open (in particular `X ∖ Z` and `Z ∖ T`) is quasi-compact
   (lem-sfb-noetherian-space-compact-subsets); the constructibility condition is the
   finite-stratification one.
2. Stratify `X` by `T`, `Z ∖ T` and `X ∖ Z`. By lem-sfb-topological-locally-closed-extension
   the restrictions of `i_* j_! L₀` to these strata are `L₀`, `0` and `0`.
3. `L₀` is pro-étale locally `O_E^r`, the pullback of the finitely presented condensed
   module `O_E^r` on the point, and `0` is the pullback of `0`; so every stratum has finite
   constant local models (det-def-sfb-constructible-local-model), and `i_* j_! L₀` is
   constructible. -/
theorem topological_integral_extension_constructible
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (T Z : Scheme.{u}) (j : T ⟶ Z) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i]
    (L₀ : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (integralCoefficientObject T ℓ E))
    (hL₀ : CondensedRing.LocallyFree (integralCoefficientObject T ℓ E) L₀) :
    IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.1) X
      (integralLowerShriek X (Profinite.padicIntegersRingObj ℓ E.1) j i L₀) :=
  isConstantModelConstructible_integralLowerShriek _ j i L₀ hL₀

end WeilConjectures.SixFunctors
