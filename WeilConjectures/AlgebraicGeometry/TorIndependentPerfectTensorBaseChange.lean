/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PullbackStalkTensorComparison
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh
import WeilConjectures.AlgebraicGeometry.SingleComplexInheritedTensorCondition
import WeilConjectures.AlgebraicGeometry.SingleComplexQcqsInduction
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.DerivedTensorQCohClosure
import WeilConjectures.AlgebraicGeometry.TorIndependentPerfectPullbackComparison
import WeilConjectures.CategoryTheory.Monoidal.DerivedBraided

/-! # Tor-independent base change for a perfect tensor factor

Source: Stacks Project, perfect.tex, single-complex base change (Tags 0DJ9, 0DJA)
and the Tor-independent comparison (Tag 08IB)
(blueprint: lem-pc-tor-independent-perfect-tensor-base-change).
-/

@[expose] public section

set_option autoImplicit false
universe uPT wPT
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

end AlgebraicGeometry
