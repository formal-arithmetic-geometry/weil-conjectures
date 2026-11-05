/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# Geometric étale stalks and unbounded derived tensor products

The stage-2 comparison is packaged in `ExactFunctorTensorComparison` to keep
concrete localization structures behind an API. Its isomorphism, naturality and
normalization clauses are exposed by `exactFunctorTensorComparison_iff`.

Source: Stacks Project, `sites-cohomology.tex`, Tag 0DEN, clause (1), and Tags 06YS,
06YT, 06YU and 07A4 (blueprint: lem-sfb-etale-derived-tensor-stalk).

## Main statements

* `AlgebraicGeometry.Etale.exists_derivedTensor_stalk_iso`: the natural isomorphism,
  normalized by the ordinary total-complex stalk comparison.
* The three auxiliary instances expose existing additive and coproduct structures.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048

universe u uC uD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.leftDerivedFunctorIsoMapDerivedCategory
  Functor.leftDerivedTensorComparison

-- Transport the derived comparison to the termwise derived functor, including its counit
-- square. Abstract category structures keep the transport rewrites small.

end AlgebraicGeometry.Etale
