/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemiRepresentableObject
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.RepresentedBy
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Hom objects and simplicial pushouts

Source: Stacks Project, Lemma 017N (blueprint: lem-weil-pbc-simplicial-hom-object-pushout).
-/

@[expose] public section

universe u₁ w₁ t₁

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.Scheme

private abbrev liftedSSet.{v, t} (S : SSet.{t}) := S ⋙ uliftFunctor.{v}

set_option linter.unusedVariables false in
set_option linter.unusedVariables false in
end AlgebraicGeometry.Scheme
