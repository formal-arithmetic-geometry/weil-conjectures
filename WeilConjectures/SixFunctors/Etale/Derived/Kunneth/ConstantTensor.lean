/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeGEInt
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Acyclic
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ConstantTensorComparison

/-!
# Tensor product with a constant complex

Let `X` be a quasi-compact quasi-separated scheme and `Λ` a commutative ring. For
`E ∈ D⁺(X_ét, Λ)` and `K ∈ D(Λ)` of Tor amplitude in `[b, ∞)`, the canonical map

`RΓ(X, E) ⊗ᴸ_Λ K ⟶ RΓ(X, E ⊗ᴸ_Λ K_X)`

is an isomorphism (`AlgebraicGeometry.Etale.isIso_constantSheafProjectionMap_of_torAmplitudeGE`).
The canonical map is the projection map of the adjunction `c_X ⊣ RΓ(X, -)`
(`CategoryTheory.Functor.mapDerivedCategoryProjectionMap`), which is the constant-tensor
comparison `AlgebraicGeometry.Etale.constantProjectionMap` (blueprint
`pur7710-def-constant-projection`) by
`AlgebraicGeometry.Etale.derivedConstantSheafProjectionMap_eq`.
Over a principal ideal domain such as `ℤ` every bounded below complex has Tor amplitude bounded
below, which gives blueprint
`lem-kun-0f0e` (Stacks, Tag 0F0E), stated over any principal ideal domain:
`AlgebraicGeometry.Etale.isIso_constantSheafProjectionMap_of_isPrincipalIdealRing`.

The projection map is an isomorphism at the unit, commutes with the shifts, and both sides are
triangulated functors of `K`, hence it is an isomorphism at the finite free modules placed in
degree `0`. Both sides commute in each degree with filtered colimits of flat modules, étale
cohomology of the quasi-compact quasi-separated scheme `X` commuting with filtered colimits, so it
is an isomorphism at the flat modules by Lazard's theorem
(`CategoryTheory.Functor.isIso_mapDerivedCategoryProjectionMap_app_singleFunctor_of_flat`).
Finally `K` is represented by a K-flat complex of flat modules vanishing below `b`, and in each
degree both sides only depend on a stupid truncation of it, a bounded complex of flat modules
(`CategoryTheory.Functor.isIso_mapDerivedCategoryProjectionMap_app_of_torAmplitudeGE`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Tensor product with a constant complex.** Let `X` be a quasi-compact quasi-separated
scheme, `E ∈ D(X_ét, Λ)` concentrated in degrees `≥ a` and `K ∈ D(Λ)` of Tor amplitude in
`[b, ∞)`. Then the canonical map `RΓ(X, E) ⊗ᴸ K ⟶ RΓ(X, E ⊗ᴸ K_X)`, the projection map of the
adjunction `c_X ⊣ RΓ(X, -)`, is an isomorphism. -/
theorem isIso_constantSheafProjectionMap_of_torAmplitudeGE (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (a : ℤ) [E.IsGE a] (K : DerivedCategory (ModuleCat.{u + 1} Λ)) (b : ℤ)
    (hK : DerivedCategory.torAmplitudeGE (ModuleCat.{u + 1} Λ) b K) :
    IsIso ((Functor.mapDerivedCategoryProjectionMap
      (derivedConstantSheafAdjunction (ModuleCat.{u + 1} Λ) X) E).app K) := by
  let Γ := Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  have hΓ (J : Type (u + 1)) [SmallCategory J] [IsFiltered J] (q : ℕ) :
      PreservesColimitsOfShape J (Γ.rightDerived q) :=
    preservesColimitsOfShape_rightDerived_globalSections_of_isFiltered Λ X q J
  exact Functor.isIso_mapDerivedCategoryProjectionMap_app_of_torAmplitudeGE
    (derivedConstantSheafAdjunction (ModuleCat.{u + 1} Λ) X)
    (fun Y n _ ↦ Γ.isGE_rightDerivedFunctor_obj Y n) E a
    (fun M hM ↦ Functor.isIso_mapDerivedCategoryProjectionMap_app_singleFunctor_of_flat (Γ := Γ)
      (derivedConstantSheafAdjunction (ModuleCat.{u + 1} Λ) X) hΓ E a M hM) K b hK

/-- Blueprint `lem-kun-0f0e`: **tensor product with a constant complex**, over a principal ideal
domain.

Let `X` be a quasi-compact quasi-separated scheme and `Λ` a principal ideal domain. For
`E ∈ D⁺(X_ét, Λ)` and `K ∈ D⁺(Λ)`, the canonical map `RΓ(X_ét, E) ⊗ᴸ_Λ K ⟶ RΓ(X_ét, E ⊗ᴸ_Λ K_X)`
is an isomorphism. The blueprint states this for `Λ = ℤ` (abelian groups are modules over the
principal ideal domain `ULift ℤ`). The canonical map is the projection map of the adjunction
`c_X ⊣ RΓ(X, -)`, equal to the constant-tensor comparison
`AlgebraicGeometry.Etale.constantProjectionMap` by
`AlgebraicGeometry.Etale.derivedConstantSheafProjectionMap_eq`. Every complex concentrated in
degrees `≥ b` has Tor amplitude in `[b - 1, ∞)`
(`DerivedCategory.torAmplitudeGE_of_isGE_of_isPrincipalIdealRing`), so this is
`AlgebraicGeometry.Etale.isIso_constantSheafProjectionMap_of_torAmplitudeGE`. -/
theorem isIso_constantSheafProjectionMap_of_isPrincipalIdealRing [IsDomain Λ]
    [IsPrincipalIdealRing Λ] (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (a : ℤ) [E.IsGE a] (K : DerivedCategory (ModuleCat.{u + 1} Λ)) (b : ℤ) [K.IsGE b] :
    IsIso ((Functor.mapDerivedCategoryProjectionMap
      (derivedConstantSheafAdjunction (ModuleCat.{u + 1} Λ) X) E).app K) :=
  isIso_constantSheafProjectionMap_of_torAmplitudeGE Λ X E a K (b - 1)
    (DerivedCategory.torAmplitudeGE_of_isGE_of_isPrincipalIdealRing K b)

end Etale

end AlgebraicGeometry
