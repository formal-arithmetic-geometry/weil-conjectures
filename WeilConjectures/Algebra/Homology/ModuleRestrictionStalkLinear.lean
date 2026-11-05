/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.Algebra.Homology.ModuleRestrictionStalkComponents
import WeilConjectures.Algebra.Homology.ModuleRestrictionStalkNaturality
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.Geometry.RingedSpace.Stalks

/-! # Scalar compatibility of restriction on module stalks

Source: Stacks Project, Sheaves Section 6.31, Lemma 6.31.1 (3),
Definition 6.31.2 (4) (Tags 009Z, 00A1).
(blueprint: lem-sc-module-restriction-stalk-linear).
-/

@[expose] public section
open CategoryTheory TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry

end AlgebraicGeometry
