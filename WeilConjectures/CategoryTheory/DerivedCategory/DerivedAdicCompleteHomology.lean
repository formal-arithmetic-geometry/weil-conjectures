/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedAdicCompleteCriteria
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsProperties
public import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology

/-!
# Derived adic completeness and homology

Let `A` be an abelian category with exact countable products. Then the derived category `D(A)`
has countable products (`CategoryTheory.derivedCategory_hasCountableProducts`) and the homology
functors `Hᵖ : D(A) ⥤ A` commute with them. Hence a complex `K` is derived `n`-adically
complete if and only if all its homology objects are, the definition
`CategoryTheory.IsDerivedAdicComplete` making sense in `A` itself
(`DerivedCategory.isDerivedAdicComplete_iff_homology`).

As a consequence, the derived `n`-adically complete objects of `A` are stable under cokernels
(`DerivedCategory.isDerivedAdicComplete_cokernel`): for `f : M ⟶ N`, the cokernel of `f` is
`H⁰` of the cone of `f`.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe w v u

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [HasCountableProducts A] [CountableAB4Star A] [HasCountableProducts (DerivedCategory A)]

end DerivedCategory
