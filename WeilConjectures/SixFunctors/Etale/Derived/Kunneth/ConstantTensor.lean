/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryProjectionFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeGEInt
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Acyclic
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FiniteCoefficients.Constant

/-!
# Tensor product with a constant complex

Let `X` be a quasi-compact quasi-separated scheme and `Λ` a commutative ring. For
`E ∈ D⁺(X_ét, Λ)` and `K ∈ D(Λ)` of Tor amplitude in `[b, ∞)`, the canonical map
(`AlgebraicGeometry.Etale.constantProjectionMap`)

`RΓ(X, E) ⊗ᴸ_Λ K ⟶ RΓ(X, E ⊗ᴸ_Λ K_X)`

is an isomorphism (`AlgebraicGeometry.Etale.isIso_constantProjectionMap_of_torAmplitudeGE`).
Over `Λ = ℤ` every bounded below complex has Tor amplitude bounded below, which gives blueprint
`lem-kun-0f0e` (Stacks, Tag 0F0E):
`AlgebraicGeometry.Etale.isIso_constantProjectionMap_int`.

The canonical map is the projection map of the adjunction `c_X ⊣ RΓ(X, -)`
(`CategoryTheory.Functor.mapDerivedCategoryProjectionMap`). It is an isomorphism at the unit,
commutes with the shifts, and both sides are triangulated functors of `K`, hence it is an
isomorphism at the finite free modules placed in degree `0`. Both sides commute in each degree
with filtered colimits of flat modules, étale cohomology of the quasi-compact quasi-separated
scheme `X` commuting with filtered colimits, so it is an isomorphism at the flat modules by
Lazard's theorem
(`CategoryTheory.Functor.isIso_mapDerivedCategoryProjectionMap_app_singleFunctor_of_flat`).
Finally `K` is represented by a K-flat complex of flat modules vanishing below `b`, and in each
degree both sides only depend on a stupid truncation of it, a bounded complex of flat modules
(`CategoryTheory.Functor.isIso_mapDerivedCategoryProjectionMap_app_of_torAmplitudeGE`).
-/

@[expose] public section

universe u u'

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Coefficients

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (W : Scheme.{u})
  [(constantSheaf W.smallEtaleTopology A).PreservesFlat]

/-- The monoidal comparison of constant complexes is the tensor comparison
`CategoryTheory.Functor.mapDerivedCategoryTensorComparison` of the functor induced by the
constant sheaf functor. -/
lemma derivedConstantSheafTensorComparison_eq (M N : DerivedCategory A) :
    derivedConstantSheafTensorComparison A W M N =
      ((Functor.mapDerivedCategoryTensorComparison
        (constantSheaf W.smallEtaleTopology A)).app M).app N := by
  rw [Functor.mapDerivedCategoryTensorComparison_app_app]
  rfl

/-- The constant-tensor comparison is the transpose of the monoidal comparison followed by the
counit. -/
lemma derivedConstantSheafProjectionMap_eq_homEquiv
    (K : DerivedCategory (Sheaf W.smallEtaleTopology A)) (M : DerivedCategory A) :
    derivedConstantSheafProjectionMap A W K M = (derivedConstantSheafAdjunction A W).homEquiv _ _
      (derivedConstantSheafTensorComparison A W _ M ≫
        (derivedConstantSheafAdjunction A W).counit.app K ▷ _) :=
  rfl

/-- The constant-tensor comparison `RΓ_W K ⊗ᴸ M ⟶ RΓ_W (K ⊗ᴸ c_W M)` is the projection map of
the adjunction `c_W ⊣ RΓ_W` (`CategoryTheory.Functor.mapDerivedCategoryProjectionMap`). -/
lemma derivedConstantSheafProjectionMap_eq (K : DerivedCategory (Sheaf W.smallEtaleTopology A))
    (M : DerivedCategory A) :
    derivedConstantSheafProjectionMap A W K M =
      (Functor.mapDerivedCategoryProjectionMap (derivedConstantSheafAdjunction A W) K).app M :=
  (derivedConstantSheafProjectionMap_eq_homEquiv A W K M).trans
    (Functor.homEquiv_comp_counit_eq_mapDerivedCategoryProjectionMap_app
      (derivedConstantSheafAdjunction A W) (derivedConstantSheafTensorComparison A W)
      (derivedConstantSheafTensorComparison_eq A W) K M)

end Coefficients

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Tensor product with a constant complex.** Let `X` be a quasi-compact quasi-separated
scheme, `E ∈ D(X_ét, Λ)` concentrated in degrees `≥ a` and `K ∈ D(Λ)` of Tor amplitude in
`[b, ∞)`. Then the canonical map `RΓ(X, E) ⊗ᴸ K ⟶ RΓ(X, E ⊗ᴸ K_X)` is an isomorphism. -/
theorem isIso_constantProjectionMap_of_torAmplitudeGE (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (a : ℤ) [E.IsGE a] (K : DerivedCategory (ModuleCat.{u + 1} Λ)) (b : ℤ)
    (hK : DerivedCategory.torAmplitudeGE (ModuleCat.{u + 1} Λ) b K) :
    IsIso (constantProjectionMap Λ X E K) := by
  let Γ := Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  have hΓ (J : Type (u + 1)) [SmallCategory J] [IsFiltered J] (q : ℕ) :
      PreservesColimitsOfShape J (Γ.rightDerived q) :=
    preservesColimitsOfShape_rightDerived_globalSections_of_isFiltered Λ X q J
  rw [constantProjectionMap, derivedConstantSheafProjectionMap_eq]
  exact Functor.isIso_mapDerivedCategoryProjectionMap_app_of_torAmplitudeGE
    (derivedConstantSheafAdjunction (ModuleCat.{u + 1} Λ) X)
    (fun Y n _ ↦ Γ.isGE_rightDerivedFunctor_obj Y n) E a
    (fun M hM ↦ Functor.isIso_mapDerivedCategoryProjectionMap_app_singleFunctor_of_flat (Γ := Γ)
      (derivedConstantSheafAdjunction (ModuleCat.{u + 1} Λ) X) hΓ E a M hM) K b hK

/-- Blueprint `lem-kun-0f0e`: **tensor product with a constant complex over `ℤ`.**

Let `X` be a quasi-compact quasi-separated scheme. For `E ∈ D⁺(X_ét, ℤ)` and `K ∈ D⁺(ℤ)`, the
canonical map `RΓ(X_ét, E) ⊗ᴸ_ℤ K ⟶ RΓ(X_ét, E ⊗ᴸ_ℤ K_X)`
(`AlgebraicGeometry.Etale.constantProjectionMap`) is an isomorphism. Abelian groups are
modules over `ULift ℤ`; a complex `K` concentrated in degrees `≥ b` has Tor amplitude in
`[b - 1, ∞)` (`DerivedCategory.torAmplitudeGE_of_isGE_int`), so this is
`AlgebraicGeometry.Etale.isIso_constantProjectionMap_of_torAmplitudeGE`. -/
theorem isIso_constantProjectionMap_int (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))))
    (a : ℤ) [E.IsGE a] (K : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) (b : ℤ)
    [K.IsGE b] :
    IsIso (constantProjectionMap (ULift.{u + 1} ℤ) X E K) :=
  isIso_constantProjectionMap_of_torAmplitudeGE _ X E a K (b - 1)
    (DerivedCategory.torAmplitudeGE_of_isGE_int K b)

end Etale

end AlgebraicGeometry
