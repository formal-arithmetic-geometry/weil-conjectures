/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.AlgebraicGeometry.AffineOpenSectionsResolutionQuasiIso
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! # Affine pushforward of an unbounded quasi-coherent resolution

Source: Stacks Project, Tags 08C2 and 0AVW.
(blueprint: lem-pc-affine-pushforward-resolution-quasi-iso).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry

end AlgebraicGeometry
