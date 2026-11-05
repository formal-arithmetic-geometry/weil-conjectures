/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.PseudoCoherentQCoh
import WeilConjectures.AlgebraicGeometry.AffineOpenLocalizedModel
import WeilConjectures.RingTheory.FiniteLocalizationFreeModel
import WeilConjectures.AlgebraicGeometry.QcOpenDerivedLift

/-! # Lifting pseudo-coherent objects from quasi-compact opens of affine schemes

Source: Stacks Project, Derived Categories of Schemes, Tag 08EE,
Lemma 36.13.3, lemma-lift-pseudo-coherent (blueprint: lem-sc-affine-pseudo-coherent-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry.Scheme
