/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenSectionTransport
public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertionBijective
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertionDifferential
import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertionAugmentation

/-! # Subset coordinates for the alternating tuple total

Source: Stacks Project, Tag 08C1, equation (20.40.0.1), and Tag 01FM.
(blueprint: lem-sc-principal-open-cech-subset-coordinates).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products

end AlgebraicGeometry
