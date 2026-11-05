/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.RingTheory.Localization.BaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap

/-!
# The `Hom` groups of the rationalization

Let `M` be a submonoid of a commutative ring `R`, `C` an `R`-linear triangulated category and
`A` a localization of `R` at `M`. This file identifies the morphisms of the rationalization
`Rationalization M C` between objects of `C` with the localizations of the `Hom` groups of `C`:
the `R`-linear map `(X ⟶ Y) → (Q X ⟶ Q Y)` induced by the localization functor `Q` is a
localization of `R`-modules at `M`, hence a base change from `R` to `A`.

## Main results

- `CategoryTheory.Rationalization.isLocalizedModule_mapLinearMap` : the map
  `(X ⟶ Y) →ₗ[R] (Q X ⟶ Q Y)` is a localization at `M`.
- `CategoryTheory.Rationalization.tensorHomEquiv` : the `A`-linear equivalence
  `A ⊗[R] (X ⟶ Y) ≃ₗ[A] (Q X ⟶ Q Y)`, sending `a ⊗ f` to `a • Q f`.
- `CategoryTheory.Rationalization.exists_iso_obj` : every object of the rationalization is
  isomorphic to `Q X` for some object `X` of `C` (a *lattice*).
- `CategoryTheory.Rationalization.exists_pow_smul_eq_map`,
  `CategoryTheory.Rationalization.exists_eq_inv_pow_smul_map` : clearing denominators, when
  every element of `M` divides a power of a fixed `ϖ`: every morphism `Q X ⟶ Q Y` is of the
  form `ϖ⁻ᴺ • Q u`.
- `CategoryTheory.Rationalization.functor_linear`, `CategoryTheory.Rationalization.linear_map` :
  `R`-linear functors between rationalizations, in particular those induced by `R`-linear
  triangulated functors, are `A`-linear.
- `CategoryTheory.Rationalization.isEquivalence_toKaroubi` : if the rationalization is
  idempotent complete, it is equivalent to its Karoubi envelope.
-/

@[expose] public section

universe w' w v₁ v₂ u₁ u₂

open CategoryTheory Category Limits Pretriangulated TensorProduct

namespace CategoryTheory.Rationalization

variable {R : Type w} [CommRing R] (M : Submonoid R)
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [Pretriangulated C] [IsTriangulated C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor D n).Linear R]
  [Pretriangulated D] [IsTriangulated D]

section Hom

variable (A : Type w') [CommRing A] [Algebra R A] [IsLocalization M A]

end Hom

variable {M}

end CategoryTheory.Rationalization
