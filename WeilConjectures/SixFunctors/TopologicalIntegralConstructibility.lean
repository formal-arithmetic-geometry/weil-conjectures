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
Noetherian setting.

## Implementation details

`X` is topologically Noetherian, hence quasi-compact and quasi-separated, and every open
immersion into a subspace of `X` is quasi-compact. Stratify `X` by `T`, `Z ∖ T` and
`X ∖ Z`: the restrictions of `i_* j_! L` to these strata are `L`, `0` and `0`, and a lisse
`L` is pro-étale locally the pullback of a finite free module on the point.

The integral statement is deduced from a version for an abstract ring object `Λ`, which
keeps the kernel from unfolding the concrete coefficient rings.

## References

* Bhatt--Scholze, Lemma 6.8.13
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A locally finite free module object over `Λ_X` is lisse. -/
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
scheme is constant-model constructible. -/
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
  rw [IsConstantModelConstructible, ite_eq_left ⟨inferInstance, inferInstance⟩]
  refine stratified_of_restrictions Λ U.ι i (by rw [hU, compl_compl]) _ ?_ ⟨R, fun a ↦ ?_⟩
  · exact finiteConstantStratified_of_isZero Λ _ _
      (CondensedRing.openRestrictionPushforwardZero Λ i U.ι hU _)
  · exact finiteModel_iso Λ _ ((CondensedRing.upperStar Λ (R.immersion a)).mapIso
      (asIso ((CondensedRing.upperStarLowerStarAdjunction Λ i).counit.app _)).symm) (hR a)

end AlgebraicGeometry.ProEtale

namespace WeilConjectures.SixFunctors

/-- For a ring object `Λ` and a locally finite free module `L` over `(coefficientRing T Λ).X`,
the extension by zero `i_* j_! L` into a topologically Noetherian scheme is constant-model
constructible. -/
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
constant-model constructible on a topologically Noetherian scheme. -/
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
