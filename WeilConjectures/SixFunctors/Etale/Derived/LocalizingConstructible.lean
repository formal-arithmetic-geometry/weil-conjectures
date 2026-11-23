/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.AffineEtaleFreeDetection
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Generation
public import WeilConjectures.ConstructibleSheaf.FreeLifting
public import WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EssentiallySmall

/-!
# `Dctf(X_ét, Λ)` generates the étale derived category

Let `k` be a field of finite cohomological dimension for `Λ`-modules, `X` a quasi-separated
`k`-scheme of finite type and `Λ` a finite ring whose exponent is invertible on `X`. The whole
derived category `D(X_ét, Λ)` is the localizing closure of `Dctf(X_ét, Λ)`
(`AlgebraicGeometry.Etale.DerivedCategory.localizingClosure_constructibleFiniteTor_eq_top`).

## Implementation details

The objects of `Dctf(X_ét, Λ)` are compact in `D(X_ét, Λ)`
(`AlgebraicGeometry.Etale.compactBoundedHom_of_constructibleFiniteTor`), and they form an
essentially small family stable under shifts. Among them are the free sheaves `Λ[U]` on the
affine étale `X`-schemes `U`, placed in degree `0`, which are constructible and flat; their shifts
detect zero objects of `D(X_ét, Λ)` (`AlgebraicGeometry.Etale.isIso_of_affineEtaleFreeComplex`).
A family of compact objects whose shifts detect zero objects generates the triangulated category
as a localizing subcategory
(`CategoryTheory.ObjectProperty.localizingClosure_eq_top_of_isCompactObj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- A small skeleton of `Dctf(X_ét, Λ)`: a family indexed by a type in `Type (u + 1)` of objects
of `Dctf(X_ét, Λ)` containing a representative of every isomorphism class, for a quasi-compact
quasi-separated scheme `X`. -/
theorem DerivedCategory.exists_skeleton_constructibleFiniteTor (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    ∃ (ι : Type (u + 1)) (S : ι → DerivedCategoryModule Λ X),
      (∀ i, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (S i)) ∧
      ∀ K, DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        ∃ i, Nonempty (S i ≅ K) := by
  have : ObjectProperty.EssentiallySmall.{u + 1}
      (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X) :=
    ObjectProperty.EssentiallySmall.of_le inf_le_left
  obtain ⟨Q, _, hQ, hP⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{u + 1}
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X)
  refine ⟨Shrink.{u + 1} (Subtype Q), fun i ↦ ((equivShrink _).symm i).1,
    fun i ↦ hQ _ ((equivShrink _).symm i).2, fun K hK ↦ ?_⟩
  obtain ⟨Y, hY, ⟨e⟩⟩ := hP K hK
  exact ⟨equivShrink _ ⟨Y, hY⟩, ⟨by simpa using e.symm⟩⟩

/-- The free sheaf `Λ[U]` on an affine étale scheme `U` over a noetherian scheme `X`, placed in
degree `0`, lies in `Dctf(X_ét, Λ)`. -/
theorem DerivedCategory.constructibleFiniteTor_affineEtaleFreeComplex {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (U : X.AffineEtale) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (affineEtaleFreeComplex Λ X U) :=
  have : IsAffine ((Scheme.AffineEtale.Spec X).obj U).left := inferInstanceAs (IsAffine (Spec _))
  have := isConstructibleSheaf_freeYoneda (Λ := Λ) ((Scheme.AffineEtale.Spec X).obj U)
  ⟨boundedConstructible_singleFunctor_obj _ _,
    0, 0, torAmplitudeIn_singleFunctor_zero_of_flat _ _ (flat_freeYoneda _)⟩

/-- **`Dctf(X_ét, Λ)` generates `D(X_ét, Λ)`.** For a finite ring `Λ` whose exponent is invertible
on a quasi-separated finite-type `k`-scheme `X`, over a field `k` of finite cohomological
dimension for `Λ`-modules, the localizing closure of `Dctf(X_ét, Λ)` is all of `D(X_ét, Λ)`. -/
theorem DerivedCategory.localizingClosure_constructibleFiniteTor_eq_top {k : Type u} [Field k]
    (hk : HasFiniteCohomologicalDimension Λ (Spec (.of k))) {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [QuasiSeparated aX]
    [HasInvertibleExponent Λ X] :
    (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).localizingClosure = ⊤ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated aX
  have := isNoetherian_of_locallyOfFiniteType aX
  refine ObjectProperty.localizingClosure_eq_top_of_isCompactObj
    (DerivedCategory.exists_skeleton_constructibleFiniteTor Λ X)
    (fun K hK ↦ (compactBoundedHom_of_constructibleFiniteTor Λ hk aX hK).1) fun Y hY ↦ ?_
  have := isIso_of_affineEtaleFreeComplex Λ X (0 : (0 : DerivedCategoryModule Λ X) ⟶ Y)
    fun U n ↦ ⟨fun _ _ _ ↦ (isZero_zero _).eq_of_tgt _ _, fun g ↦ ⟨0, by
      dsimp only
      rw [comp_zero, hY _ ((DerivedCategory.constructibleFiniteTor _ X).le_shift n _
        (DerivedCategory.constructibleFiniteTor_affineEtaleFreeComplex Λ U)) g]⟩⟩
  exact (isZero_zero _).of_iso (asIso (0 : (0 : DerivedCategoryModule Λ X) ⟶ Y)).symm

end AlgebraicGeometry.Etale
