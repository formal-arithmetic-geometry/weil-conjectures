/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseExtensionConstructible
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseRestriction
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement

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
namespace WeilConjectures.SixFunctors

/-- Extension by zero along an open immersion followed by a closed immersion of a locally
free module over an arbitrary commutative condensed ring is constant-model constructible
on a topologically Noetherian scheme. -/
theorem isConstantModelConstructible_openClosedExtension
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    {T Z : Scheme.{u}} (j : T ⟶ Z) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    (L₀ : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hL₀ : CondensedRing.LocallyFree (condensedRingObj Λ T) L₀) :
    IsConstantModelConstructible Λ X (integralLowerShriek X Λ j i L₀) := by
  have : TopologicalSpace.NoetherianSpace Z := i.isEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace T := j.isEmbedding.isInducing.noetherianSpace
  have hs := stratified_openExtension Λ j L₀
    (stratified_of_finiteModel Λ T L₀ (lisse_finiteModel Λ T L₀ (lisse_of_raw_free Λ T L₀ hL₀)))
  let U := Scheme.openComplementOfIsClosedImmersion i
  have : TopologicalSpace.NoetherianSpace U.toScheme := U.ι.isEmbedding.isInducing.noetherianSpace
  have hij : Set.range U.ι = (Set.range i)ᶜ := by
    simp [U, Scheme.openComplementOfIsClosedImmersion]
  have hji : Set.range i = (Set.range U.ι)ᶜ := by rw [hij, compl_compl]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ⟨e⟩, _⟩ :=
    CondensedRing.condensed_open_closed_recollement Λ i U.ι hij
  have hc : CompactSpace X := inferInstance
  have hq : QuasiSeparatedSpace X := inferInstance
  rw [IsConstantModelConstructible, if_pos (And.intro hc hq)]
  apply stratified_of_restrictions Λ U.ι i hji
  · exact finiteConstantStratified_of_isZero Λ _ _
      (CondensedRing.openRestrictionPushforwardZero Λ i U.ι hij _)
  · obtain ⟨R, hR⟩ := hs
    refine ⟨R, fun a ↦ ?_⟩
    exact finiteModel_iso Λ _
      ((CondensedRing.upperStar Λ (R.immersion a)).mapIso (e.app _).symm) (hR a)

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
      (integralLowerShriek X (Profinite.padicIntegersRingObj ℓ E.1) j i L₀) := by
  exact isConstantModelConstructible_openClosedExtension _ X j i L₀ hL₀

end WeilConjectures.SixFunctors
