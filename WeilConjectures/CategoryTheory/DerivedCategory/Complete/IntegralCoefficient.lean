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
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!

# Derived complete objects with coefficients in the ring of integers of an `ℓ`-adic field

This file specializes `DerivedCategory.derivedComplete` of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs` to the coefficient ring of
the integral stage of the `ℓ`-adic formalism: `E` is an extension of `ℚ_ℓ` inside `ℚ̄_ℓ`,
`𝒪_E` is its ring of integers and `𝔪_E` is the maximal ideal of `𝒪_E`. The site is the
small pro-étale site `X.ProEt` of a scheme `X`, with the pro-étale topology
`Scheme.ProEt.topology X`. This file defines the full subcategory

```
  D_comp(X, 𝒪_E)  ⊆  D(X, 𝒪_E) := DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat 𝒪_E))
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

`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs` takes an essentially small site
with objects in `Type (u + 1)` and morphisms in `Type u` — the shape of the small pro-étale
site `X.ProEt` of a `Scheme.{u}` — and its coefficient ring in `Type (u + 1)`. The field `E`
lives in an arbitrary universe `Type w` and is assumed `Small.{u + 1}`, so the coefficient ring
used below is the copy `Shrink.{u + 1} (PadicAlgCl.integers l E)` of `𝒪_E` in `Type (u + 1)`.
`Shrink` carries the ring structure across (`Shrink.ringEquiv`), so no instance has to be
replayed by hand; the one fact that does need transporting, `IsAdicComplete`, is
transported along `PadicAlgCl.shrinkRingEquiv` by `IsAdicComplete.congr_ringEquiv`.

## Main definitions

- `DerivedCategory.derivedCompleteIntegral` : the property of an object of `D(X, 𝒪_E)` of being
  derived complete with respect to `𝔪_E`.
- `DerivedCategoryDerivedCompleteIntegral` : the full subcategory `D_comp(X, 𝒪_E)` of derived
  complete objects, and `DerivedCategoryDerivedCompleteIntegral.ι` its inclusion into
  `D(X, 𝒪_E)`.

## Main results

- `DerivedCategory.isTriangulated_derivedCompleteIntegral` : the derived complete objects form a
  triangulated subcategory of `D(X, 𝒪_E)` (currently `sorry`), so that `D_comp(X, 𝒪_E)` is
  an `𝒪_E`-linear triangulated category with `𝒪_E`-linear shift functors.
- `DerivedCategory.derivedCompleteIntegral_iff_isIso_lift` : when `R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)`
  exists, membership in `D_comp(X, 𝒪_E)` says exactly that the canonical map
  `K ⟶ R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)` is an isomorphism.

-/


@[expose] public section

universe w u

open AlgebraicGeometry CategoryTheory Limits

section DerivedComplete

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type w) [Field E]
  [Algebra E (PadicAlgCl l)] [Small.{u + 1} E]

/-- An object `K` of the derived category `D(X, 𝒪_E)` of sheaves of `𝒪_E`-modules on the
small pro-étale site of `X` is *derived complete* if it is derived complete for the maximal
ideal `𝔪_E` of `𝒪_E` in the sense of `DerivedCategory.derivedComplete`: the cone of the
reduction maps `K ⟶ K ⊗ᴸ 𝒪_E/𝔪_Eⁿ`, whose point is `K` itself, is a limit cone. -/
noncomputable abbrev DerivedCategory.derivedCompleteIntegral :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))))) :=
  DerivedCategory.derivedComplete (Scheme.ProEt.topology X) (PadicAlgCl.maximalIdealShrink l E)

/-- The category `D_comp(X, 𝒪_E)` of derived complete objects, realized as the full
subcategory of `D(X, 𝒪_E)` cut out by `DerivedCategory.derivedCompleteIntegral`. This is the
integral stage of the `ℓ`-adic formalism: the coefficients are the ring of integers `𝒪_E`
of an extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ = PadicAlgCl l`, and completeness is taken with
respect to the maximal ideal of `𝒪_E`. -/
noncomputable def DerivedCategoryDerivedCompleteIntegral : Type _ :=
  (DerivedCategory.derivedCompleteIntegral X l E).FullSubcategory

noncomputable instance : Category (DerivedCategoryDerivedCompleteIntegral X l E) :=
  inferInstanceAs <| Category (DerivedCategory.derivedCompleteIntegral X l E).FullSubcategory

/-- The inclusion of `D_comp(X, 𝒪_E)` into the derived category of sheaves of
`𝒪_E`-modules. -/
noncomputable def DerivedCategoryDerivedCompleteIntegral.ι :
    DerivedCategoryDerivedCompleteIntegral X l E ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))) :=
  (DerivedCategory.derivedCompleteIntegral X l E).ι

/-- The derived complete objects of `D(X, 𝒪_E)` form a triangulated subcategory: they
contain `0` and are stable under shifts and extensions.

The proof is currently `sorry`. -/
instance DerivedCategory.isTriangulated_derivedCompleteIntegral :
    (DerivedCategory.derivedCompleteIntegral X l E).IsTriangulated :=
  sorry

noncomputable instance : Preadditive (DerivedCategoryDerivedCompleteIntegral X l E) :=
  inferInstanceAs <| Preadditive (DerivedCategory.derivedCompleteIntegral X l E).FullSubcategory

/-- The `Hom` groups of `D_comp(X, 𝒪_E)` are `𝒪_E`-modules, as those of `D(X, 𝒪_E)` are. -/
noncomputable instance :
    Linear (Shrink.{u + 1} (PadicAlgCl.integers l E))
      (DerivedCategoryDerivedCompleteIntegral X l E) :=
  inferInstanceAs <| Linear (Shrink.{u + 1} (PadicAlgCl.integers l E))
    (DerivedCategory.derivedCompleteIntegral X l E).FullSubcategory

noncomputable instance : HasZeroObject (DerivedCategoryDerivedCompleteIntegral X l E) :=
  inferInstanceAs <| HasZeroObject (DerivedCategory.derivedCompleteIntegral X l E).FullSubcategory

noncomputable instance : HasShift (DerivedCategoryDerivedCompleteIntegral X l E) ℤ :=
  inferInstanceAs <| HasShift (DerivedCategory.derivedCompleteIntegral X l E).FullSubcategory ℤ

instance (n : ℤ) : (shiftFunctor (DerivedCategoryDerivedCompleteIntegral X l E) n).Additive :=
  inferInstanceAs <|
    (shiftFunctor (DerivedCategory.derivedCompleteIntegral X l E).FullSubcategory n).Additive

/-- The shift functors of `D_comp(X, 𝒪_E)` are `𝒪_E`-linear, as those of `D(X, 𝒪_E)` are. -/
instance (n : ℤ) :
    (shiftFunctor (DerivedCategoryDerivedCompleteIntegral X l E) n).Linear
      (Shrink.{u + 1} (PadicAlgCl.integers l E)) :=
  inferInstanceAs <|
    (shiftFunctor (DerivedCategory.derivedCompleteIntegral X l E).FullSubcategory n).Linear
      (Shrink.{u + 1} (PadicAlgCl.integers l E))

noncomputable instance : Pretriangulated (DerivedCategoryDerivedCompleteIntegral X l E) :=
  inferInstanceAs <| Pretriangulated (DerivedCategory.derivedCompleteIntegral X l E).FullSubcategory

instance : IsTriangulated (DerivedCategoryDerivedCompleteIntegral X l E) :=
  inferInstanceAs <| IsTriangulated (DerivedCategory.derivedCompleteIntegral X l E).FullSubcategory

variable {X l E}

/-- If the limit `R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)` exists, then `K` lies in `D_comp(X, 𝒪_E)`
precisely when the canonical map `K ⟶ R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)` is an isomorphism. -/
lemma DerivedCategory.derivedCompleteIntegral_iff_isIso_lift
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    [HasLimit (derivedCompletionDiagram (Scheme.ProEt.topology X)
      (PadicAlgCl.maximalIdealShrink l E) K)] :
    derivedCompleteIntegral X l E K ↔
      IsIso (limit.lift (derivedCompletionDiagram (Scheme.ProEt.topology X)
          (PadicAlgCl.maximalIdealShrink l E) K)
        (derivedCompletionCone (Scheme.ProEt.topology X) (PadicAlgCl.maximalIdealShrink l E) K)) :=
  derivedComplete_iff_isIso_lift K

end DerivedComplete
