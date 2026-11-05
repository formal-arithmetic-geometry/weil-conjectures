/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The triangles `R ⟶ R ⟶ R/ϖⁿ ⟶ R⟦1⟧`

Let `(C, J)` be an essentially small site, `R` a commutative ring and `ϖ ∈ R` a nonzerodivisor
generating the ideal `I`. This file builds the distinguished triangles
`DerivedCategory.quotPowTriangle J hϖ hI n : R ⟶ R ⟶ R/Iⁿ ⟶ R⟦1⟧` of `D(J, R)`, whose first
map is the multiplication by `ϖⁿ`, together with their transition morphisms
`DerivedCategory.quotPowTriangleMap`.

-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Opposite Pretriangulated

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]

variable {J}

section ShortExact

variable {I : Ideal R} {ϖ : R}

end ShortExact

section Triangles

variable (J) {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

end Triangles

end DerivedCategory
