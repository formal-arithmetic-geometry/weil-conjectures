/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Finite section homology from cokernel and homology acyclicity

Source: Stacks Project, Tags 015B and 08C2.
(blueprint: lem-sc-affine-basis-acyclic-sections-preserves-homology).
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules

end AlgebraicGeometry
