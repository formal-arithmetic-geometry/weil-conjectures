/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization

/-!

# Constructible objects with coefficients in an `ℓ`-adic field

Let `E` be an extension of `ℚ_ℓ` inside `ℚ̄_ℓ = PadicAlgCl l`, with ring of integers
`𝒪_E = PadicAlgCl.integers l E`. This file passes from the category `D_cons(X, 𝒪_E)` of
constructible objects of the derived category of sheaves of `𝒪_E`-modules on the small
pro-étale site `X.ProEt` of a scheme `X`
(`WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient`) to the category
`D_cons(X, E)` with coefficients in `E`.

## Inverting the nonzero elements of `𝒪_E`

`D_cons(X, E)` is the rationalization of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization`,

```
  D_cons(X, E)  :=  D_cons(X, 𝒪_E) / (torsion objects),
```

the Verdier quotient of `D_cons(X, 𝒪_E)` by the triangulated subcategory of objects killed
by a nonzero element of `𝒪_E`; equivalently, the localization of `D_cons(X, 𝒪_E)` at the
morphisms whose mapping cone is killed by a nonzero element of `𝒪_E`. It is a triangulated
category, and it is `E`-linear because `E` is the fraction field of `𝒪_E`
(`PadicAlgCl.isFractionRing_shrink`).

When `E` is finite over `ℚ_ℓ`, `𝒪_E` is a discrete valuation ring in which `ℓ` is a nonzero
element of the maximal ideal, so every nonzero element of `𝒪_E` divides a power of `ℓ`, and
an object is killed by a nonzero element of `𝒪_E` if and only if it is killed by a power of
`ℓ`: this is the same category as `D_cons(X, 𝒪_E)[1/ℓ]`, the case `M = Submonoid.powers ℓ`
of the rationalization; inverting all nonzero elements makes the `E`-linear structure come
directly from `IsFractionRing 𝒪_E E`.

The Verdier quotient needs `D_cons(X, 𝒪_E)` to be triangulated, i.e. the constructible
objects to form a triangulated subcategory of `D(X, 𝒪_E)`
(`DerivedCategory.isTriangulated_constructibleIntegral` in
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient`); this is
currently `sorry`.

## Main definitions

- `PadicAlgCl.algebraShrink`, `PadicAlgCl.isFractionRing_shrink` : `E` is the fraction field
  of the universe `u + 1` copy `Shrink 𝒪_E` of its ring of integers.
- `DerivedCategoryConstructibleRational` : the triangulated, `E`-linear category
  `D_cons(X, E)`.
- `DerivedCategoryConstructibleRational.fromIntegral` : the localization functor
  `D_cons(X, 𝒪_E) ⥤ D_cons(X, E)`.

-/

@[expose] public section

universe w u

open AlgebraicGeometry CategoryTheory Limits

section RingOfIntegers

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E]

/-- `E` as an algebra over the universe `u + 1` copy `Shrink 𝒪_E` of its ring of integers,
through `Shrink.ringEquiv : Shrink 𝒪_E ≃+* 𝒪_E`. -/
noncomputable instance algebraShrink : Algebra (Shrink.{u + 1} (integers l E)) E :=
  ((algebraMap (integers l E) E).comp (Shrink.ringEquiv (integers l E)).toRingHom).toAlgebra

/-- `E` is the fraction field of the universe `u + 1` copy `Shrink 𝒪_E` of its ring of
integers, as it is of `𝒪_E` itself. -/
instance isFractionRing_shrink : IsFractionRing (Shrink.{u + 1} (integers l E)) E :=
  IsFractionRing.of_ringEquiv_left (Shrink.ringEquiv (integers l E)) fun _ ↦ rfl

end PadicAlgCl

end RingOfIntegers

section ECoefficient

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime] (E : Type w) [Field E]
  [Algebra E (PadicAlgCl l)] [Small.{u + 1} E]

/-- The category `D_cons(X, E)` of constructible objects with coefficients in the `ℓ`-adic
field `E`: the rationalization of `D_cons(X, 𝒪_E)` at the nonzero elements of `𝒪_E`, i.e.
its Verdier quotient by the objects killed by a nonzero element of `𝒪_E`. Since
`E = 𝒪_E[1/ℓ]`, this is `D_cons(X, 𝒪_E)[1/ℓ]`. It is triangulated and `E`-linear. -/
@[reducible]
def DerivedCategoryConstructibleRational : Type _ :=
  Rationalization (nonZeroDivisors (Shrink.{u + 1} (PadicAlgCl.integers l E)))
    (DerivedCategoryConstructibleIntegral X l E)

/-- The `Hom` groups of `D_cons(X, E)` are `E`-vector spaces. -/
noncomputable example : Linear E (DerivedCategoryConstructibleRational X l E) := inferInstance

example : IsTriangulated (DerivedCategoryConstructibleRational X l E) := inferInstance

/-- The localization functor `D_cons(X, 𝒪_E) ⥤ D_cons(X, E)`. -/
@[reducible]
noncomputable def DerivedCategoryConstructibleRational.fromIntegral :
    DerivedCategoryConstructibleIntegral X l E ⥤ DerivedCategoryConstructibleRational X l E :=
  Rationalization.Q _ _

end ECoefficient
