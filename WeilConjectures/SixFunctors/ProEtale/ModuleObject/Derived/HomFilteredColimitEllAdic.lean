/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralLfpLocallyFreeResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomFilteredColimitConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClFlat

import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-!
# Continuity of `Hom` out of constructible sheaves with `ℓ`-adic coefficients

Blueprint `sk-lem-constructible-ext-continuity` (1), and `sk-lem-int-ext` (1) for `𝒪_E`: for the
`ℓ`-adic coefficient rings `Λ = E, 𝒪_E, ℚ̄_ℓ` and a separated finite-type scheme `X` over a field,
morphisms `C ⟶ B[n]` out of a constructible sheaf `C` into a filtered colimit `B = colim Bᵢ` of
sheaves factor through some `Bᵢ[n]`:

* `hasConstructibleExtContinuity_continuousMapRingObj_of_locallyOfFiniteType`,
* `hasConstructibleExtContinuity_padicIntegersRingObj_of_locallyOfFiniteType`,
* `hasConstructibleExtContinuity_padicAlgClRingObj_of_locallyOfFiniteType`.

They follow from the dévissage
`homCommutesWithFilteredColimits_singleFunctor_of_isConstructibleModuleObject`,
whose two hypotheses are verified here:

* flatness of `Λ_X` over `ℤ`, from the torsion-freeness of continuous maps into `Λ`
  (`AlgebraicGeometry.ProEtale.preservesMonomorphisms_tensorLeft_continuousMapComparison`);
* the case of lisse sheaves `L` on a scheme with noetherian underlying space: for the fields `E`
  and `ℚ̄_ℓ` such an `L` is locally free, and for `𝒪_E` it has a resolution
  `0 ⟶ F₁ ⟶ F₀ ⟶ L ⟶ 0` by locally free sheaves (`integral_lfp_locallyFree_resolution`); locally
  free sheaves are handled by
  `homCommutesWithFilteredColimits_singleFunctor_of_isLocallyFree`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### Flatness -/

/-- For a finite extension `E` of `ℚ_ℓ`, `E_X = p_X^* E̲` is flat over `ℤ`. -/
theorem preservesFiniteLimits_tensorLeft_continuousMapRingObj_of_finiteDimensional
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u}) :
    PreservesFiniteLimits
      (tensorLeft (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X)) := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] E).injective
  have := preservesMonomorphisms_tensorLeft_continuousMapComparison X E
  exact preservesFiniteLimits_tensorLeft_of_preservesMonomorphisms X _

/-- For a subfield `E` of `ℚ̄_ℓ`, `𝒪_{E,X} = p_X^* 𝒪̲_E` is flat over `ℤ`. -/
theorem preservesFiniteLimits_tensorLeft_padicIntegersRingObj_of_algebra (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    (X : Scheme.{u}) :
    PreservesFiniteLimits
      (tensorLeft (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : NormedAlgebra ℚ_[ℓ] E :=
    { norm_smul_le c x := by
        change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] E).injective
  have : IsAddTorsionFree E := inferInstance
  have := preservesMonomorphisms_tensorLeft_continuousMapComparison X (PadicAlgCl.integers ℓ E)
  exact preservesFiniteLimits_tensorLeft_of_preservesMonomorphisms X _

/-! ### Lisse sheaves -/

/-- Blueprint `sk-lem-constructible-ext-continuity`, lisse case for `E`: on a scheme with
noetherian underlying space, `Hom(L[0], -[n])` commutes with filtered colimits for every locally
finitely presented `E_X`-module `L`, which is locally free. -/
theorem homCommutesWithFilteredColimits_singleFunctor_continuousMapRingObj (E : Type)
    [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X))
    (hL : IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj E) X) L) :
    DerivedCategory.HomCommutesWithFilteredColimits.{u + 1}
      ((DerivedCategory.singleFunctor _ 0).obj L) :=
  have := preservesFiniteLimits_tensorLeft_continuousMapRingObj_of_finiteDimensional ℓ E X
  homCommutesWithFilteredColimits_singleFunctor_of_isLocallyFree _ X (continuous_lf ℓ E X L hL)

/-- Blueprints `sk-lem-constructible-ext-continuity` and `sk-lem-int-ext` (1), lisse case for
`𝒪_E`: on a scheme with noetherian underlying space, `Hom(L[0], -[n])` commutes with filtered
colimits for every locally finitely presented `𝒪_{E,X}`-module `L`. Indeed `L` has a resolution
`0 ⟶ F₁ ⟶ F₀ ⟶ L ⟶ 0` by locally free modules. -/
theorem homCommutesWithFilteredColimits_singleFunctor_padicIntegersRingObj (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X))
    (hL : IsLocallyFinitelyPresented
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X) L) :
    DerivedCategory.HomCommutesWithFilteredColimits.{u + 1}
      ((DerivedCategory.singleFunctor _ 0).obj L) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : NormedAlgebra ℚ_[ℓ] E :=
    { norm_smul_le c x := by
        change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  have : PreservesFiniteLimits
      (tensorLeft (condensedRingObj (CondensedRing.integralCoeff ℓ E) X)) :=
    preservesFiniteLimits_tensorLeft_padicIntegersRingObj_of_algebra ℓ E X
  obtain ⟨F₁, F₀, f, g, w, hS, h₁, h₀⟩ := integral_lfp_locallyFree_resolution X ℓ E L hL
  exact DerivedCategory.HomCommutesWithFilteredColimits.ext₃ _ hS.singleTriangle_distinguished
    (homCommutesWithFilteredColimits_singleFunctor_of_isLocallyFree _ X h₁)
    (homCommutesWithFilteredColimits_singleFunctor_of_isLocallyFree _ X h₀)

/-- Blueprint `sk-lem-constructible-ext-continuity`, lisse case for `ℚ̄_ℓ`: on a scheme with
noetherian underlying space, `Hom(L[0], -[n])` commutes with filtered colimits for every locally
finitely presented `ℚ̄_{ℓ,X}`-module `L`, which is locally free. -/
theorem homCommutesWithFilteredColimits_singleFunctor_padicAlgClRingObj (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X))
    (hL : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) L) :
    DerivedCategory.HomCommutesWithFilteredColimits.{u + 1}
      ((DerivedCategory.singleFunctor _ 0).obj L) :=
  homCommutesWithFilteredColimits_singleFunctor_of_isLocallyFree _ X
    (isLocallyFree_of_isLocallyFinitelyPresented_of_noetherianSpace ℓ X hL)

/-! ### Constructible sheaves -/

variable {k : Type u} [Field k]

/-- Blueprint `sk-lem-constructible-ext-continuity` (1), for the coefficient ring `E` of a finite
extension `E` of `ℚ_ℓ` and a separated finite-type `k`-scheme `X`: `Ext^q(C, -)` out of a
constructible `E`-sheaf `C` commutes with filtered colimits of sheaves. -/
theorem hasConstructibleExtContinuity_continuousMapRingObj_of_locallyOfFiniteType (E : Type)
    [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    HasConstructibleExtContinuity (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := {}
  exact fun M hM ↦ (homCommutesWithFilteredColimits_singleFunctor_of_isConstructibleModuleObject
    _ (preservesFiniteLimits_tensorLeft_continuousMapRingObj_of_finiteDimensional ℓ E)
    (fun _ _ ↦ homCommutesWithFilteredColimits_singleFunctor_continuousMapRingObj ℓ E _)
    X M hM).homFactorsThroughFilteredColimits

/-- Blueprint `sk-lem-int-ext` (1), for the coefficient ring `𝒪_E` of a finite extension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a separated finite-type `k`-scheme `X`: `Ext^q(C, -)` out of a
constructible `𝒪_E`-sheaf `C` commutes with filtered colimits of sheaves. -/
theorem hasConstructibleExtContinuity_padicIntegersRingObj_of_locallyOfFiniteType (E : Type)
    [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    HasConstructibleExtContinuity
      (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := {}
  exact fun M hM ↦ (homCommutesWithFilteredColimits_singleFunctor_of_isConstructibleModuleObject
    _ (preservesFiniteLimits_tensorLeft_padicIntegersRingObj_of_algebra ℓ E)
    (fun _ _ ↦ homCommutesWithFilteredColimits_singleFunctor_padicIntegersRingObj ℓ E _)
    X M hM).homFactorsThroughFilteredColimits

/-- Blueprint `sk-lem-constructible-ext-continuity` (1), for the coefficient ring `ℚ̄_ℓ` and a
separated finite-type `k`-scheme `X`: `Ext^q(C, -)` out of a constructible `ℚ̄_ℓ`-sheaf `C`
commutes with filtered colimits of sheaves. -/
theorem hasConstructibleExtContinuity_padicAlgClRingObj_of_locallyOfFiniteType {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX] :
    HasConstructibleExtContinuity (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := {}
  exact fun M hM ↦ (homCommutesWithFilteredColimits_singleFunctor_of_isConstructibleModuleObject
    _ (fun Y ↦ preservesFiniteLimits_tensorLeft_padicAlgClRingObj Y ℓ)
    (fun _ _ ↦ homCommutesWithFilteredColimits_singleFunctor_padicAlgClRingObj ℓ _)
    X M hM).homFactorsThroughFilteredColimits

end AlgebraicGeometry.ProEtale.CondensedRing
