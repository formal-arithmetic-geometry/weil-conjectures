/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationMap

/-!

# The morphisms of a rationalization

Let `C` be an `R`-linear triangulated category and `M` a submonoid of `R`. Blueprint
`def-weil-rationalization-karoubi` describes the rationalization `C[1/ϖ]` as the category with
the same objects as `C` and morphisms `Hom_C(K, L) ⊗_{𝒪_E} E`. For the rationalization
`CategoryTheory.Rationalization M C` (the Verdier quotient by the `M`-torsion objects) this file
proves that description: the map `Hom_C(K, L) ⟶ Hom_{C[1/M]}(K, L)` induced by the localization
functor is a localization of `R`-modules at `M` (`IsLocalizedModule`), so that
`Hom_{C[1/M]}(K, L) ≅ M⁻¹ Hom_C(K, L)`, which is `Hom_C(K, L) ⊗_R M⁻¹R`
(`IsLocalizedModule.isBaseChange`); every object of the rationalization comes from `C`.

## Main definitions

- `CategoryTheory.Rationalization.mapLinearMap`: the `R`-linear map
  `Hom_C(X, Y) ⟶ Hom_{C[1/M]}(X, Y)`.
- `CategoryTheory.Rationalization.homLinearEquiv`: `Hom_{C[1/M]}(X, Y) ≃ M⁻¹ Hom_C(X, Y)`.

## Main statements

- `CategoryTheory.Rationalization.isLocalizedModule_mapLinearMap`: the map is a localization
  at `M`.
- `CategoryTheory.Rationalization.essSurj_Q`: the localization functor is essentially surjective
  (indeed bijective on objects up to the identity of the underlying type).

-/

@[expose] public section

universe w v u

open CategoryTheory Category Limits Pretriangulated

namespace CategoryTheory.Rationalization

variable {R : Type w} [CommRing R] (M : Submonoid R)
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [Pretriangulated C] [IsTriangulated C]

/-- The `R`-linear map `Hom_C(X, Y) ⟶ Hom_{C[1/M]}(X, Y)` induced by the localization functor
`CategoryTheory.Rationalization.Q`. -/
noncomputable def mapLinearMap (X Y : C) :
    (X ⟶ Y) →ₗ[R] ((Q M C).obj X ⟶ (Q M C).obj Y) where
  toFun f := (Q M C).map f
  map_add' _ _ := (Q M C).map_add
  map_smul' r f := (Q M C).map_smul r f

@[simp]
lemma mapLinearMap_apply {X Y : C} (f : X ⟶ Y) : mapLinearMap M X Y f = (Q M C).map f :=
  rfl

/-- Blueprint `def-weil-rationalization-karoubi`: Rationalization (scalar localization), the
morphisms. The morphisms of the rationalization `C[1/M]` between objects of `C` are the
localization at `M` of the morphisms of `C`: `Hom_{C[1/M]}(X, Y) = M⁻¹ Hom_C(X, Y)`. For
`R = 𝒪_E` and `M` its nonzero elements, this is `Hom_C(X, Y) ⊗_{𝒪_E} E`. -/
theorem isLocalizedModule_mapLinearMap (X Y : C) :
    IsLocalizedModule M (mapLinearMap M X Y) where
  map_units m := by
    have := isIso_smul_id m.2 ((Q M C).obj X)
    rw [Module.End.isUnit_iff]
    constructor
    · intro φ₁ φ₂ h
      exact smul_left_injective m.2 h
    · intro φ
      refine ⟨inv ((m : R) • 𝟙 ((Q M C).obj X)) ≫ φ, ?_⟩
      change (m : R) • (inv ((m : R) • 𝟙 ((Q M C).obj X)) ≫ φ) = φ
      rw [show ((m : R) • (inv ((m : R) • 𝟙 ((Q M C).obj X)) ≫ φ)) =
          (((m : R) • 𝟙 ((Q M C).obj X)) ≫ inv ((m : R) • 𝟙 ((Q M C).obj X))) ≫ φ by
        rw [Linear.smul_comp, id_comp, Linear.smul_comp], IsIso.hom_inv_id, id_comp]
  surj φ := by
    obtain ⟨m, hm, f, h⟩ := exists_smul_eq_map φ
    exact ⟨⟨f, ⟨m, hm⟩⟩, h⟩
  exists_of_eq {f g} h := by
    obtain ⟨m, hm, h'⟩ := (map_eq_map_iff f g).1 h
    exact ⟨⟨m, hm⟩, h'⟩

/-- The morphisms of the rationalization between objects of `C`, as the localized module
`M⁻¹ Hom_C(X, Y)`. -/
noncomputable def homLinearEquiv (X Y : C) :
    LocalizedModule M (X ⟶ Y) ≃ₗ[R] ((Q M C).obj X ⟶ (Q M C).obj Y) :=
  have := isLocalizedModule_mapLinearMap M X Y
  IsLocalizedModule.iso M (mapLinearMap M X Y)

/-- Every object of the rationalization is the image of an object of `C`: the rationalization
has the same objects as `C`. -/
instance essSurj_Q : (Q M C).EssSurj :=
  Localization.essSurj (Q M C) (W M C)

end CategoryTheory.Rationalization
