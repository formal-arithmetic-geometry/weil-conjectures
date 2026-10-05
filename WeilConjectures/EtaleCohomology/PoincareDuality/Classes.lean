/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

/-!
# Cohomology classes and the coefficient ring of a geometric point

The degreewise statements of the Poincaré duality chapter pair cohomology *classes*. The
repository has no Künneth map on the cohomology objects `H^i` and no lax monoidal structure
on `RΓ`, so the pairings are not defined on the objects
`AlgebraicGeometry.Etale.compactlySupportedCohomology`. Instead they use the convention of
`WeilConjectures.SixFunctors.Etale.Derived.Supports`: a class of degree `i` of an object
`M ∈ D(T_ét, Λ)` is a morphism `Λ_T ⟶ M[i]`. For the structure morphism `a : X ⟶ s` of a
scheme over `s = Spec k`, the classes of `Ra_! K` and of `Ra_* K` in `D(s_ét, Λ)` are
`H^i_c(X, K)` and `H^i(X, K)`.

The classes form a `Λ`-module, because `D(T_ét, Λ)` is `Λ`-linear: the category of sheaves
of `Λ`-modules is `Λ`-linear as a full subcategory of presheaves (`Linear.fullSubcategory`),
and Mathlib makes the derived category of a `Λ`-linear abelian category `Λ`-linear
(`DerivedCategory.instLinear`). For `s = Spec k` the endomorphisms of the unit `Λ_s` are
`H^0(Spec k, Λ) = Λ` (`AlgebraicGeometry.Etale.bijective_smul_id_unit`), which is what makes
pairings of classes `Λ`-valued (`AlgebraicGeometry.Etale.coefficientRingEquiv`).

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.cohomologyClasses M i`: the classes `Λ_T ⟶ M[i]`.
- `AlgebraicGeometry.Etale.coefficientRingEquiv`: `Λ ≃+* End (Λ_s)` for `s = Spec k`.
- `AlgebraicGeometry.Etale.coefficientLinearMap`: its inverse, as a `Λ`-linear map.

## Main statements

- `AlgebraicGeometry.Etale.bijective_smul_id_unit`: `r ↦ r • 𝟙` is a bijection
  `Λ ≃ End (Λ_s)`.
- `AlgebraicGeometry.Etale.linear_derivedTensor_obj`,
  `AlgebraicGeometry.Etale.linear_derivedTensor_flip_obj`: the derived tensor product of
  `D(T_ét, Λ)` is `Λ`-linear in each variable.

## Implementation notes

The linearity of the derived tensor product in each variable is stated, not proved: the
monoidal structure on `D(T_ét, Λ)` is the abstract one of
`WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`, and its
compatibility with the additive and `Λ`-linear structures is not yet formalised. It is what
makes the cup products and the degreewise pairings bilinear. It is stated for the functors
`K ⊗ᴸ -` and `- ⊗ᴸ K` rather than as `CategoryTheory.MonoidalLinear`, because statements
about `D(T_ét, ModuleCat Λ)` must be written with `AlgebraicGeometry.Etale.derivedTensor`
(see `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {Λ} in
/-- Tensoring with a fixed complex, `M ↦ K ⊗ᴸ M`, is additive on `D(T_ét, Λ)`. -/
instance additive_derivedTensor_obj {T : Scheme.{u}}
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) T).obj K).Additive :=
  sorry

/-- Tensoring with a fixed complex, `M ↦ K ⊗ᴸ M`, is `Λ`-linear on `D(T_ét, Λ)`. -/
instance linear_derivedTensor_obj {T : Scheme.{u}}
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) T).obj K).Linear Λ :=
  sorry

variable {Λ} in
/-- Tensoring with a fixed complex, `M ↦ M ⊗ᴸ K`, is additive on `D(T_ét, Λ)`. -/
instance additive_derivedTensor_flip_obj {T : Scheme.{u}}
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) T).flip.obj K).Additive :=
  sorry

/-- Tensoring with a fixed complex, `M ↦ M ⊗ᴸ K`, is `Λ`-linear on `D(T_ét, Λ)`. -/
instance linear_derivedTensor_flip_obj {T : Scheme.{u}}
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) T).flip.obj K).Linear Λ :=
  sorry

variable {Λ} in
/-- The *cohomology classes of degree `i`* of an object `M` of `D(T_ét, Λ)`: the morphisms
`Λ_T ⟶ M[i]` out of the unit, the constant complex `Λ_T`. For `M = Ra_! K` and `M = Ra_* K`
in `D(s_ét, Λ)`, with `a : X ⟶ s` and `s = Spec k`, these are `H^i_c(X, K)` and
`H^i(X, K)`; for `M = Λ_X` in `D(X_ét, Λ)` they are `H^i(X, Λ)`. They form a `Λ`-module,
`D(T_ét, Λ)` being `Λ`-linear. -/
abbrev DerivedCategory.cohomologyClasses {T : Scheme.{u}}
    (M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (i : ℤ) :=
  𝟙_ (_root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) ⟶ M⟦i⟧

variable (k : Type u) [Field k]

/-- The endomorphisms of the constant complex `Λ_s` of `s = Spec k` are the scalars:
`r ↦ r • 𝟙` is a bijection from `Λ` onto `End (Λ_s) = H^0(Spec k, Λ)`. The étale site of
`Spec k` is the category of finite étale `k`-algebras, and `Spec k` is connected, so
`H^0(Spec k, Λ) = Λ`. -/
theorem bijective_smul_id_unit :
    Function.Bijective (fun r : Λ ↦ r • 𝟙 (𝟙_ (DerivedCategory
      (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))))) :=
  sorry

/-- The coefficient ring `Λ` is the ring of endomorphisms of the constant complex `Λ_s` of
`s = Spec k`, through `r ↦ r • 𝟙` (`AlgebraicGeometry.Etale.bijective_smul_id_unit`).
Through its inverse, morphisms `Λ_s ⟶ Λ_s`, such as the values of the degreewise pairings,
are read as scalars. -/
noncomputable def coefficientRingEquiv :
    Λ ≃+* End (𝟙_ (DerivedCategory
      (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)))) :=
  RingEquiv.ofBijective (algebraMap Λ _) (by
    convert bijective_smul_id_unit Λ k using 1
    ext r
    exact Algebra.algebraMap_eq_smul_one r)

/-- The inverse `End (Λ_s) ⟶ Λ` of `AlgebraicGeometry.Etale.coefficientRingEquiv`, as a
`Λ`-linear map. -/
noncomputable def coefficientLinearMap :
    End (𝟙_ (DerivedCategory
      (Sheaf (Spec (CommRingCat.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)))) →ₗ[Λ] Λ where
  toFun := (coefficientRingEquiv Λ k).symm
  map_add' := map_add _
  map_smul' r φ := by
    rw [Algebra.smul_def, map_mul, RingHom.id_apply, smul_eq_mul]
    congr 1
    exact (coefficientRingEquiv Λ k).symm_apply_apply r

end Etale

end AlgebraicGeometry
