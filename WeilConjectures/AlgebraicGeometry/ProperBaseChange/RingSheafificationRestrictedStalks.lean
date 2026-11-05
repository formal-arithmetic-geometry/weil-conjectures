/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Final

/-! # Restricted ring sheafification units on abelian stalks

Source: Stacks Project, Sheaves, Lemmas 007Z and 0087; restriction to an open subspace.
(blueprint: lem-weil-pbc-ring-sheafification-restricted-stalks).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open Opposite TopologicalSpace
namespace AlgebraicGeometry

end AlgebraicGeometry
