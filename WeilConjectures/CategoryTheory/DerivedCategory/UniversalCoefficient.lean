/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Flat.TorsionFree
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Universal coefficient sequences

Let `R` be a commutative ring and `x ∈ R`. For a distinguished triangle
`C ⟶[x] C ⟶ D ⟶ C⟦1⟧` of `D(R)` whose first map is the multiplication by `x` (for example
`D = C ⊗ᴸ R/(x)` when `x` is a nonzerodivisor), the long exact homology sequence breaks up into
the *universal coefficient sequences*

`0 ⟶ Hⁱ(C) ⊗_R R/(x) ⟶ Hⁱ(D) ⟶ Hⁱ⁺¹(C)[x] ⟶ 0`,

where `M[x]` is the `x`-torsion of `M`; for a nonzerodivisor `x` it is `Tor₁^R(M, R/(x))`.

## Main definitions

- `ModuleCat.universalCoefficientShortComplex`: the short complex
  `A ⊗ R/(x) ⟶ B ⟶ A'[x]` attached to maps `A ⟶ B ⟶ A'` with `A ⟶[x] A ⟶ B` and
  `B ⟶ A' ⟶[x] A'` zero.
- `DerivedCategory.universalCoefficientSequence`: the universal coefficient sequence of a
  triangle `C ⟶[x] C ⟶ D ⟶ C⟦1⟧`.

## Main statements

- `ModuleCat.universalCoefficientShortComplex_shortExact`: the short complex is short exact
  when `A ⟶[x] A ⟶ B ⟶ A' ⟶[x] A'` is exact.
- `DerivedCategory.universalCoefficientSequence_shortExact`: the universal coefficient sequence
  of a distinguished triangle is short exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped TensorProduct

namespace ModuleCat

variable {R : Type u} [CommRing R] (x : R)

section

variable {A B A' : ModuleCat.{u} R} (f : A ⟶ B) (g : B ⟶ A')

end

section Tor

open MonoidalCategory ZeroObject

variable {x}

variable [Small.{u} R]

end Tor

end ModuleCat

namespace DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory (ModuleCat.{u} R)] (x : R)

variable {x} {C D : DerivedCategory (ModuleCat.{u} R)} {g : C ⟶ D} {h : D ⟶ C⟦(1 : ℤ)⟧}
  (hT : Triangle.mk (x • 𝟙 C) g h ∈ distTriang _) (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁)

end DerivedCategory

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C) {A₁ A₂ A₃ : C}
  (e₁ : S.X₁ ≅ A₁) (e₂ : S.X₂ ≅ A₂) (e₃ : S.X₃ ≅ A₃)

end CategoryTheory.ShortComplex
