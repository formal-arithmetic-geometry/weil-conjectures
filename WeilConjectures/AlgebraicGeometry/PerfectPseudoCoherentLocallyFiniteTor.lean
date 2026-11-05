/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.LocallyFiniteTorDimension
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectFiniteFreeRefinement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Perfect complexes are pseudo-coherent and locally of finite Tor dimension
Source: literature/stacks-project/cohomology.tex, Lemma 08CQ, implication (1) => (2)
(blueprint: lem-pc-perfect-pseudo-coherent-locally-finite-tor).
-/

@[expose] public section

universe uP wP
open CategoryTheory
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
