/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.Modules.GenericRank

/-! # Pulling back fibrewise zero sections through a reduced scheme

Source: Stacks Project, Schemes, Tag 01J1 (reduced schemes), applied in a local basis;
Varieties, Tag 0FD6, final paragraph of lemma-bertini.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

attribute [local irreducible] tensorPullback tensorPullbackObj tensorPullbackSection

end AlgebraicGeometry.Scheme.Modules
