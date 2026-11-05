/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
public import WeilConjectures.AlgebraicGeometry.DerivedTensorAugmentation
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import all WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedLocalizations
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedRestrictionSquare
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Structure and restriction comparisons for a spectrum presentation

Source: Stacks Project, Tag 08DC; Mathlib exact functors and scheme-module restriction.
(blueprint: lem-sc-spectrum-structure-restriction-comparison).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry.Scheme
