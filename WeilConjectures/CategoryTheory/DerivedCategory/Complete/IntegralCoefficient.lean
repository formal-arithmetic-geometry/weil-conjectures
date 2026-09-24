/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import WeilConjectures.NumberTheory.Padics.Extension
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!

# Derived complete objects with coefficients in the ring of integers of an `ℓ`-adic field

This file specializes `DerivedCategory.derivedComplete` of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs` to the coefficient ring of
the integral stage of the `ℓ`-adic formalism: `E` is an extension of `ℚ_ℓ` inside `ℚ̄_ℓ`,
`𝒪_E` is its ring of integers and `𝔪_E` is the maximal ideal of `𝒪_E`. For a site `(C, J)`
it defines the full subcategory

```
  D_comp(J, 𝒪_E)  ⊆  D(J, 𝒪_E) := DerivedCategory (Sheaf J (ModuleCat 𝒪_E))
```

of those objects that are derived complete for `𝔪_E`, together with its inclusion functor.

## The hypotheses on `E`

The field `E` is given together with `[Algebra ℚ_[l] E] [Algebra E (PadicAlgCl l)]
[IsScalarTower ℚ_[l] E (PadicAlgCl l)]`: an extension of `ℚ_ℓ` with a `ℚ_ℓ`-embedding into
the fixed algebraic closure `ℚ̄_ℓ = PadicAlgCl l`. Its ring of integers
`PadicAlgCl.integers l E`, the valuation subring of the valuation restricted from `ℚ̄_ℓ`, is
set up in `WeilConjectures.NumberTheory.Padics.Extension`.

The ring of integers and the categories below only use the embedding `E → ℚ̄_ℓ`. The
`ℚ_ℓ`-algebra structure, the scalar tower and finiteness `[FiniteDimensional ℚ_[l] E]` are
used for the completeness of `𝒪_E` (`PadicAlgCl.isAdicComplete_integers`).

## Universes

`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs` takes its site `(C, J)` with
objects in `Type (u + 1)` and morphisms in `Type u` — the shape of the small étale site of
a `Scheme.{u}` — and its coefficient ring in `Type (u + 1)`. The field `E` lives in an
arbitrary universe `Type w` and is assumed `Small.{u + 1}`, so the coefficient ring used
below is the copy `Shrink.{u + 1} (PadicAlgCl.integers l E)` of `𝒪_E` in `Type (u + 1)`.
`Shrink` carries the ring structure across (`Shrink.ringEquiv`), so no instance has to be
replayed by hand; the one fact that does need transporting, `IsAdicComplete`, is
transported along `PadicAlgCl.shrinkRingEquiv` by `IsAdicComplete.congr_ringEquiv`.

## Main definitions

- `DerivedCategory.derivedCompleteIntegral` : the property of an object of `D(J, 𝒪_E)` of being
  derived complete with respect to `𝔪_E`.
- `DerivedCategoryDerivedCompleteIntegral` : the full subcategory `D_comp(J, 𝒪_E)` of derived
  complete objects, and `DerivedCategoryDerivedCompleteIntegral.ι` its inclusion into
  `D(J, 𝒪_E)`.
- `DerivedCategoryDerivedCompleteIntegral.completion` : the derived completion
  `D(J, 𝒪_E) ⥤ D_comp(J, 𝒪_E)`, the left adjoint of the inclusion, for `E` finite over `ℚ_ℓ`
  (its existence, `DerivedCategoryDerivedCompleteIntegral.isRightAdjoint_ι`, is currently
  `sorry`).

## Main results

- `DerivedCategory.isTriangulated_derivedCompleteIntegral` : the derived complete objects form a
  triangulated subcategory of `D(J, 𝒪_E)` (currently `sorry`), so that `D_comp(J, 𝒪_E)` is
  an `𝒪_E`-linear triangulated category with `𝒪_E`-linear shift functors.
- `DerivedCategory.derivedCompleteIntegral_iff_isIso_lift` : when `R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)`
  exists, membership in `D_comp(J, 𝒪_E)` says exactly that the canonical map
  `K ⟶ R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)` is an isomorphism.

-/


@[expose] public section

universe w u

open CategoryTheory Limits

section DerivedComplete

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (l : ℕ) [Fact l.Prime] (E : Type w) [Field E]
  [Algebra E (PadicAlgCl l)] [Small.{u + 1} E]

/-- An object `K` of the derived category `D(J, 𝒪_E)` of sheaves of `𝒪_E`-modules on a site
`(C, J)` is *derived complete* if it is derived complete for the maximal ideal `𝔪_E` of
`𝒪_E` in the sense of `DerivedCategory.derivedComplete`: the cone of the reduction maps
`K ⟶ K ⊗ᴸ 𝒪_E/𝔪_Eⁿ`, whose point is `K` itself, is a limit cone. -/
noncomputable abbrev DerivedCategory.derivedCompleteIntegral :
    ObjectProperty
      (DerivedCategory (Sheaf J (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))))) :=
  DerivedCategory.derivedComplete J (PadicAlgCl.maximalIdealShrink l E)

/-- The category `D_comp(J, 𝒪_E)` of derived complete objects, realized as the full
subcategory of `D(J, 𝒪_E)` cut out by `DerivedCategory.derivedCompleteIntegral`. This is the
integral stage of the `ℓ`-adic formalism: the coefficients are the ring of integers `𝒪_E`
of an extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ = PadicAlgCl l`, and completeness is taken with
respect to the maximal ideal of `𝒪_E`. -/
noncomputable def DerivedCategoryDerivedCompleteIntegral : Type _ :=
  (DerivedCategory.derivedCompleteIntegral J l E).FullSubcategory

noncomputable instance : Category (DerivedCategoryDerivedCompleteIntegral J l E) :=
  inferInstanceAs <| Category (DerivedCategory.derivedCompleteIntegral J l E).FullSubcategory

/-- The inclusion of `D_comp(J, 𝒪_E)` into the derived category of sheaves of
`𝒪_E`-modules. -/
noncomputable def DerivedCategoryDerivedCompleteIntegral.ι :
    DerivedCategoryDerivedCompleteIntegral J l E ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))) :=
  (DerivedCategory.derivedCompleteIntegral J l E).ι

/-- The derived complete objects of `D(J, 𝒪_E)` form a triangulated subcategory: they
contain `0` and are stable under shifts and extensions.

The proof is currently `sorry`. -/
instance DerivedCategory.isTriangulated_derivedCompleteIntegral :
    (DerivedCategory.derivedCompleteIntegral J l E).IsTriangulated :=
  sorry

noncomputable instance : Preadditive (DerivedCategoryDerivedCompleteIntegral J l E) :=
  inferInstanceAs <| Preadditive (DerivedCategory.derivedCompleteIntegral J l E).FullSubcategory

/-- The `Hom` groups of `D_comp(J, 𝒪_E)` are `𝒪_E`-modules, as those of `D(J, 𝒪_E)` are. -/
noncomputable instance :
    Linear (Shrink.{u + 1} (PadicAlgCl.integers l E))
      (DerivedCategoryDerivedCompleteIntegral J l E) :=
  inferInstanceAs <| Linear (Shrink.{u + 1} (PadicAlgCl.integers l E))
    (DerivedCategory.derivedCompleteIntegral J l E).FullSubcategory

noncomputable instance : HasZeroObject (DerivedCategoryDerivedCompleteIntegral J l E) :=
  inferInstanceAs <| HasZeroObject (DerivedCategory.derivedCompleteIntegral J l E).FullSubcategory

noncomputable instance : HasShift (DerivedCategoryDerivedCompleteIntegral J l E) ℤ :=
  inferInstanceAs <| HasShift (DerivedCategory.derivedCompleteIntegral J l E).FullSubcategory ℤ

instance (n : ℤ) : (shiftFunctor (DerivedCategoryDerivedCompleteIntegral J l E) n).Additive :=
  inferInstanceAs <|
    (shiftFunctor (DerivedCategory.derivedCompleteIntegral J l E).FullSubcategory n).Additive

/-- The shift functors of `D_comp(J, 𝒪_E)` are `𝒪_E`-linear, as those of `D(J, 𝒪_E)` are. -/
instance (n : ℤ) :
    (shiftFunctor (DerivedCategoryDerivedCompleteIntegral J l E) n).Linear
      (Shrink.{u + 1} (PadicAlgCl.integers l E)) :=
  inferInstanceAs <|
    (shiftFunctor (DerivedCategory.derivedCompleteIntegral J l E).FullSubcategory n).Linear
      (Shrink.{u + 1} (PadicAlgCl.integers l E))

noncomputable instance : Pretriangulated (DerivedCategoryDerivedCompleteIntegral J l E) :=
  inferInstanceAs <| Pretriangulated (DerivedCategory.derivedCompleteIntegral J l E).FullSubcategory

instance : IsTriangulated (DerivedCategoryDerivedCompleteIntegral J l E) :=
  inferInstanceAs <| IsTriangulated (DerivedCategory.derivedCompleteIntegral J l E).FullSubcategory

variable {J l E}

/-- If the limit `R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)` exists, then `K` lies in `D_comp(J, 𝒪_E)`
precisely when the canonical map `K ⟶ R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)` is an isomorphism. -/
lemma DerivedCategory.derivedCompleteIntegral_iff_isIso_lift
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    [HasLimit (derivedCompletionDiagram J (PadicAlgCl.maximalIdealShrink l E) K)] :
    derivedCompleteIntegral J l E K ↔
      IsIso (limit.lift (derivedCompletionDiagram J (PadicAlgCl.maximalIdealShrink l E) K)
        (derivedCompletionCone J (PadicAlgCl.maximalIdealShrink l E) K)) :=
  derivedComplete_iff_isIso_lift K

end DerivedComplete

section Completion

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (l : ℕ) [Fact l.Prime] (E : Type w) [Field E]
  [Algebra ℚ_[l] E] [Algebra E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] [Small.{u + 1} E]

/-- The inclusion of `D_comp(J, 𝒪_E)` into `D(J, 𝒪_E)` has a left adjoint, the *derived
completion* `K ↦ R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)`. Since `E` is finite over `ℚ_ℓ`, the maximal
ideal `𝔪_E` is principal and each `𝒪_E/𝔪_Eⁿ` is a perfect `𝒪_E`-module, which is what makes
the completion derived complete and the unit `K ⟶ K^` universal.

The proof is currently `sorry`. -/
instance DerivedCategoryDerivedCompleteIntegral.isRightAdjoint_ι :
    (DerivedCategoryDerivedCompleteIntegral.ι J l E).IsRightAdjoint :=
  sorry

/-- The derived completion functor `D(J, 𝒪_E) ⥤ D_comp(J, 𝒪_E)`, the left adjoint of the
inclusion `DerivedCategoryDerivedCompleteIntegral.ι`. -/
noncomputable def DerivedCategoryDerivedCompleteIntegral.completion :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))) ⥤
      DerivedCategoryDerivedCompleteIntegral J l E :=
  (DerivedCategoryDerivedCompleteIntegral.ι J l E).leftAdjoint

/-- The derived completion is left adjoint to the inclusion of the derived complete objects. -/
noncomputable def DerivedCategoryDerivedCompleteIntegral.completionAdjunction :
    DerivedCategoryDerivedCompleteIntegral.completion J l E ⊣
      DerivedCategoryDerivedCompleteIntegral.ι J l E :=
  Adjunction.ofIsRightAdjoint _

end Completion
