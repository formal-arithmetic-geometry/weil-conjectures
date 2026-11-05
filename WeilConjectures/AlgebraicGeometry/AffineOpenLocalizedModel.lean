/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.AlgebraicGeometry.AffineModuleComplexRepresentative
import WeilConjectures.AlgebraicGeometry.AffineOpenPseudoCoherentLocalizationPoint
import WeilConjectures.AlgebraicGeometry.AffinePrincipalCoverQuasiIsoDetection

/-! # Affine module models on a quasi-compact open

Source: Stacks Project, Tag 08EE, module-model reduction and final sheafification
(blueprint: lem-sc-affine-open-localized-model).
-/

@[expose] public section

set_option autoImplicit false

universe u w wL

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry.Scheme
