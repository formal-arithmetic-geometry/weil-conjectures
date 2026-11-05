/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The derived restriction square of a scheme isomorphism

Source: Stacks Project, Tag 09IR, isomorphism transport in the affine setup;
Mathlib scheme-module restriction composition and localization uniqueness.
(blueprint: lem-pc-scheme-iso-derived-restriction-square).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry.Scheme
