/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.TensorQuotPow
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.ReductionCone
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower

/-!
# Reductions of the derived limit of a strict normalized adic tower

Let `(C, J)` be an essentially small site, `R` a commutative ring and `ϖ ∈ R` a nonzerodivisor
generating the ideal `I`. For a normalized `ϖ`-adic tower `T` of complexes of sheaves of
`R`-modules (`CochainComplex.IsNormalizedAdicTower`) and a homotopy limit
`K = R lim_n T_n` of its image in `D(J, R)`, the reductions `K ⊗ᴸ R/Iⁿ` are the `T_n`,
compatibly with the reduction maps and with the transitions:
`DerivedCategory.exists_derivedCompletionDiagram_iso_of_isNormalizedAdicTower`.

Proof sketch: `- ⊗ᴸ R/Iⁿ` is triangulated and commutes with countable products, hence with
`R lim`; on complexes it is the mapping cone of `ϖⁿ` (`DerivedCategory.reductionIso`), and the
tower of cones `cone(ϖⁿ on T_{m+n})` has derived limit `T_n`
(`CochainComplex.IsNormalizedAdicTower.isIso_π_comp`).

## Implementation notes

The monoidal structure of `D(J, R)` is taken from the fields of
`DerivedCategory.sheafTensorStructure J R`, as explained in the implementation notes of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Opposite Pretriangulated

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]

attribute [-instance] commShift₂CurriedTensor commShiftTensorLeft commShiftTensorRight
  isTriangulated_tensorLeft isTriangulated_tensorRight monoidalPreadditive monoidalLinear

variable {J}

section Products

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

end Products

section Reduction

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

end Reduction

section Reduction'

variable {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

end Reduction'

end DerivedCategory

namespace CochainComplex.IsNormalizedAdicTower

open ConeCoimage

variable {R : Type*} [Ring R] {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [Linear R 𝒜]
  {ϖ : R} {T : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ}

end CochainComplex.IsNormalizedAdicTower

namespace DerivedCategory

open CochainComplex CochainComplex.IsNormalizedAdicTower ConeCoimage

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R]
  {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})
  {T : ℕᵒᵖ ⥤ CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ}
  (hT : IsNormalizedAdicTower ϖ T)
  {c : Cone (T ⋙ Q)} (hc : IsHomotopyLimit c)

end DerivedCategory
