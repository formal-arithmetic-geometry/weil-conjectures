/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.FiniteStructureProductCore

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
open Scheme.Modules
set_option autoImplicit false
/-- The lifted product is multiplicative after every finite reduction.

Source: Stacks Project, Tags 09ZT, 088E and 088F. The proof follows the
compatibility of the finite direct-image products with base change and the
tensor comparison, then evaluates the resulting morphism identity on sections.
(blueprint: lem-weil-pbc-finite-structure-product-compatibility). -/
theorem finite_structure_product_compatibility :
    type_of% @finite_structure_product_exists_core :=
  @finite_structure_product_exists_core

end AlgebraicGeometry
