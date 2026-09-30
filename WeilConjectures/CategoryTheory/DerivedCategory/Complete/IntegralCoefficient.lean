/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ChangeOfRings
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.TorDimension
public import WeilConjectures.ConstructibleSheaf.ProEtale
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
public import WeilConjectures.NumberTheory.Padics.Extension
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!

# Derived complete and constructible objects with coefficients in `𝒪_E`

This file specializes `DerivedCategory.derivedComplete` of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs` to the coefficient ring of
the integral stage of the `ℓ`-adic formalism: `E` is an extension of `ℚ_ℓ` inside `ℚ̄_ℓ`,
`𝒪_E` is its ring of integers and `𝔪_E` is the maximal ideal of `𝒪_E`. The site is the
small pro-étale site `X.ProEt` of a scheme `X`, with the pro-étale topology
`Scheme.ProEt.topology X`. This file defines the properties of an object of

```
  D(X, 𝒪_E) := DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat 𝒪_E))
```

of being derived complete for `𝔪_E`, and of being constructible in the sense of
[Stacks 09C1]: derived complete, with derived reduction modulo `𝔪_E` having constructible
homology sheaves and locally finite tor dimension.

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
replayed by hand; the facts that do need transporting along `PadicAlgCl.shrinkRingEquiv` are
that `Shrink 𝒪_E` is a local ring (`PadicAlgCl.isLocalRing_shrink`), so that `𝔪_E` is its
`IsLocalRing.maximalIdeal`, and that it is complete for it (`PadicAlgCl.isAdicComplete_shrink`).

## Main definitions

- `DerivedCategory.derivedCompleteIntegral` : the property of an object of `D(X, 𝒪_E)` of being
  derived complete with respect to `𝔪_E`.
- `DerivedCategory.constructibleIntegral` : the property of an object `K` of
  `D(X, 𝒪_E)` of being derived complete with `K ⊗ᴸ_{𝒪_E} 𝒪_E/𝔪_E` having constructible
  homology sheaves and locally finite tor dimension, the derived reduction being the derived
  extension of scalars `DerivedCategory.algebraExtendScalars` of
  `WeilConjectures.CategoryTheory.DerivedCategory.ChangeOfRings`.
- `DerivedCategoryConstructibleIntegral` : the full subcategory `D_cons(X, 𝒪_E)` of
  constructible objects, an `𝒪_E`-linear triangulated category with `𝒪_E`-linear shift
  functors, and `DerivedCategoryConstructibleIntegral.ι` its inclusion into `D(X, 𝒪_E)`.

## Main results

- `DerivedCategory.isTriangulated_constructibleIntegral` : the constructible objects form a
  triangulated subcategory of `D(X, 𝒪_E)` (currently `sorry`).

- `DerivedCategory.isTriangulated_derivedCompleteIntegral` : the derived complete objects form a
  triangulated subcategory of `D(X, 𝒪_E)` (currently `sorry`).
- `DerivedCategory.derivedCompleteIntegral_iff_isIso_lift` : when `R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)`
  exists, `K` is derived complete exactly when the canonical map
  `K ⟶ R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)` is an isomorphism.

-/


@[expose] public section

universe w u

open AlgebraicGeometry CategoryTheory IsLocalRing Limits

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
  DerivedCategory.derivedComplete (Scheme.ProEt.topology X)
    (maximalIdeal (Shrink.{u + 1} (PadicAlgCl.integers l E)))

/-- The derived complete objects of `D(X, 𝒪_E)` form a triangulated subcategory: they
contain `0` and are stable under shifts and extensions.

The proof is currently `sorry`. -/
instance DerivedCategory.isTriangulated_derivedCompleteIntegral :
    (DerivedCategory.derivedCompleteIntegral X l E).IsTriangulated :=
  sorry

variable {X l E}

/-- If the limit `R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)` exists, then `K` is derived complete precisely
when the canonical map `K ⟶ R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ)` is an isomorphism. -/
lemma DerivedCategory.derivedCompleteIntegral_iff_isIso_lift
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    [HasLimit (derivedCompletionDiagram (Scheme.ProEt.topology X)
      (maximalIdeal (Shrink.{u + 1} (PadicAlgCl.integers l E))) K)] :
    derivedCompleteIntegral X l E K ↔
      IsIso (limit.lift (derivedCompletionDiagram (Scheme.ProEt.topology X)
          (maximalIdeal (Shrink.{u + 1} (PadicAlgCl.integers l E))) K)
        (derivedCompletionCone (Scheme.ProEt.topology X)
          (maximalIdeal (Shrink.{u + 1} (PadicAlgCl.integers l E))) K)) :=
  derivedComplete_iff_isIso_lift K

end DerivedComplete

section ConstructibleHomology

variable (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})

/-- An object of the derived category of pro-étale sheaves of `Λ`-modules has constructible
homology if all its homology sheaves are constructible
(`AlgebraicGeometry.ProEtale.IsConstructibleSheaf`). This is the pro-étale counterpart of
`AlgebraicGeometry.Etale.DerivedCategory.constructibleHomology`. -/
noncomputable def AlgebraicGeometry.ProEtale.DerivedCategory.constructibleHomology :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :=
  fun M ↦ ∀ n : ℤ, ProEtale.IsConstructibleSheaf Λ ((DerivedCategory.homologyFunctor _ n).obj M)

end ConstructibleHomology

section Constructible

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type w) [Field E]
  [Algebra E (PadicAlgCl l)] [Small.{u + 1} E]

/-- An object `K` of `D(X, 𝒪_E)` is *constructible* in the sense of [Stacks 09C1] if

1. `K` is derived complete with respect to `𝔪_E` (`DerivedCategory.derivedCompleteIntegral`);
2. the derived reduction `K ⊗ᴸ_{𝒪_E} 𝒪_E/𝔪_E`, computed by the derived extension of scalars
   `DerivedCategory.algebraExtendScalars` along `𝒪_E → 𝒪_E/𝔪_E`, has constructible homology
   sheaves (`ProEtale.DerivedCategory.constructibleHomology`) and locally has finite tor
   dimension (`DerivedCategory.locallyFiniteTorDimension`, [Stacks 08FY]). -/
noncomputable def DerivedCategory.constructibleIntegral :
    ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))))) :=
  derivedCompleteIntegral X l E ⊓ ObjectProperty.inverseImage
    (ProEtale.DerivedCategory.constructibleHomology
        (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸
          maximalIdeal (Shrink.{u + 1} (PadicAlgCl.integers l E))) X ⊓
      locallyFiniteTorDimension (Scheme.ProEt.topology X)
        (Shrink.{u + 1} (PadicAlgCl.integers l E) ⧸
          maximalIdeal (Shrink.{u + 1} (PadicAlgCl.integers l E))))
    (algebraExtendScalars (Scheme.ProEt.topology X) _ _)

/-- The constructible objects of `D(X, 𝒪_E)` form a triangulated subcategory: they contain
`0` and are stable under shifts and extensions.

The proof is currently `sorry`. -/
instance DerivedCategory.isTriangulated_constructibleIntegral :
    (DerivedCategory.constructibleIntegral X l E).IsTriangulated :=
  sorry

/-- The category `D_cons(X, 𝒪_E)` of constructible objects [Stacks 09C1], realized as the
full subcategory of `D(X, 𝒪_E)` cut out by `DerivedCategory.constructibleIntegral`. This is
the integral stage of the `ℓ`-adic formalism: the coefficients are the ring of integers
`𝒪_E` of an extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ = PadicAlgCl l`. -/
noncomputable def DerivedCategoryConstructibleIntegral : Type _ :=
  (DerivedCategory.constructibleIntegral X l E).FullSubcategory

noncomputable instance : Category (DerivedCategoryConstructibleIntegral X l E) :=
  inferInstanceAs <| Category (DerivedCategory.constructibleIntegral X l E).FullSubcategory

/-- The inclusion of `D_cons(X, 𝒪_E)` into the derived category of sheaves of
`𝒪_E`-modules. -/
noncomputable def DerivedCategoryConstructibleIntegral.ι :
    DerivedCategoryConstructibleIntegral X l E ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))) :=
  (DerivedCategory.constructibleIntegral X l E).ι

noncomputable instance : Preadditive (DerivedCategoryConstructibleIntegral X l E) :=
  inferInstanceAs <| Preadditive (DerivedCategory.constructibleIntegral X l E).FullSubcategory

/-- The `Hom` groups of `D_cons(X, 𝒪_E)` are `𝒪_E`-modules, as those of `D(X, 𝒪_E)` are. -/
noncomputable instance :
    Linear (Shrink.{u + 1} (PadicAlgCl.integers l E))
      (DerivedCategoryConstructibleIntegral X l E) :=
  inferInstanceAs <| Linear (Shrink.{u + 1} (PadicAlgCl.integers l E))
    (DerivedCategory.constructibleIntegral X l E).FullSubcategory

noncomputable instance : HasZeroObject (DerivedCategoryConstructibleIntegral X l E) :=
  inferInstanceAs <| HasZeroObject (DerivedCategory.constructibleIntegral X l E).FullSubcategory

noncomputable instance : HasShift (DerivedCategoryConstructibleIntegral X l E) ℤ :=
  inferInstanceAs <| HasShift (DerivedCategory.constructibleIntegral X l E).FullSubcategory ℤ

instance (n : ℤ) : (shiftFunctor (DerivedCategoryConstructibleIntegral X l E) n).Additive :=
  inferInstanceAs <|
    (shiftFunctor (DerivedCategory.constructibleIntegral X l E).FullSubcategory n).Additive

/-- The shift functors of `D_cons(X, 𝒪_E)` are `𝒪_E`-linear, as those of `D(X, 𝒪_E)` are. -/
instance (n : ℤ) :
    (shiftFunctor (DerivedCategoryConstructibleIntegral X l E) n).Linear
      (Shrink.{u + 1} (PadicAlgCl.integers l E)) :=
  inferInstanceAs <|
    (shiftFunctor (DerivedCategory.constructibleIntegral X l E).FullSubcategory n).Linear
      (Shrink.{u + 1} (PadicAlgCl.integers l E))

noncomputable instance : Pretriangulated (DerivedCategoryConstructibleIntegral X l E) :=
  inferInstanceAs <| Pretriangulated (DerivedCategory.constructibleIntegral X l E).FullSubcategory

instance : IsTriangulated (DerivedCategoryConstructibleIntegral X l E) :=
  inferInstanceAs <| IsTriangulated (DerivedCategory.constructibleIntegral X l E).FullSubcategory

noncomputable instance : (DerivedCategoryConstructibleIntegral.ι X l E).CommShift ℤ :=
  inferInstanceAs <| (DerivedCategory.constructibleIntegral X l E).ι.CommShift ℤ

instance : (DerivedCategoryConstructibleIntegral.ι X l E).IsTriangulated :=
  inferInstanceAs <| (DerivedCategory.constructibleIntegral X l E).ι.IsTriangulated

end Constructible
