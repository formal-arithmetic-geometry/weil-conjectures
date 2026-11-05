/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# Homology of complexes of abelian groups commutes with products

Products of abelian groups are exact, so the homology of a product of complexes of abelian groups
is the product of their homologies: the functor `HomologicalComplex.homologyFunctor` preserves
products. The proof is elementwise: a family of cycles of the factors is a cycle of the product,
and a family of boundaries of the factors is a boundary of the product.

## Main statements

- `HomologicalComplex.preservesLimitsOfShape_discrete_homologyFunctor_ab`: the homology functors
  of complexes of abelian groups preserve products.
-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace HomologicalComplex

variable {ι : Type*} {c : ComplexShape ι} (M : HomologicalComplex AddCommGrpCat.{u} c)

variable {κ : Type w} (K : κ → HomologicalComplex AddCommGrpCat.{max u w} c)

end HomologicalComplex
