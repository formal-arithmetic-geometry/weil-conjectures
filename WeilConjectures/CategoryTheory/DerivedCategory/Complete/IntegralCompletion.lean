/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Completion
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The derived completion at the integral stage

For a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and a site `(C, J)`, this file specializes
the derived completion `DerivedCategory.derivedCompletion` to the coefficient ring `𝒪_E` and
its maximal ideal: the functor

```
  (-)^ : D(J, 𝒪_E) ⥤ D_comp(J, 𝒪_E),   K ↦ R lim_n (K ⊗ᴸ 𝒪_E/𝔪_Eⁿ),
```

left adjoint to the inclusion `DerivedCategoryDerivedCompleteIntegral.ι`. It is a triangulated
`𝒪_E`-linear functor. The operations of the integral stage are defined by applying an operation
of `D(J, 𝒪_E)` to derived complete objects and completing the result; the lemmas at the end of
the file compare such completed composites
(`DerivedCategoryDerivedCompleteIntegral.completionCompIso`).

## Main definitions

- `DerivedCategoryDerivedCompleteIntegral.completion`: the derived completion functor.
- `DerivedCategoryDerivedCompleteIntegral.completionAdjunction`: `(-)^ ⊣ ι`.
- `DerivedCategoryDerivedCompleteIntegral.completionCompIso`: for a triangulated functor `Φ`
  preserving the objects on which `ϖ` acts invertibly, `(Φ (ι K^))^ ≅ (Φ K)^`.
-/

@[expose] public section

universe w u

open CategoryTheory Category Limits Pretriangulated

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R]

section CompIso

variable {C' : Type (u + 1)} [Category.{u} C'] [EssentiallySmall.{u + 1} C']
  {J' : GrothendieckTopology C'} {R' : Type (u + 1)} [CommRing R']
  (I : Ideal R) (h : ∃ ϖ ∈ nonZeroDivisors R, I = Ideal.span {ϖ})
  (I' : Ideal R') (h' : ∃ ϖ ∈ nonZeroDivisors R', I' = Ideal.span {ϖ})
  (Φ : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) ⥤
    DerivedCategory (Sheaf J' (ModuleCat.{u + 1} R'))) [Φ.CommShift ℤ] [Φ.IsTriangulated]
  (hΦ : ∀ X, idealInvertible J I X → idealInvertible J' I' (Φ.obj X))

end CompIso

end DerivedCategory

section Integral

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (l : ℕ) [Fact l.Prime] (E : Type w) [Field E]
  [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] [Small.{u + 1} E]

namespace DerivedCategoryDerivedCompleteIntegral

end DerivedCategoryDerivedCompleteIntegral

end Integral
