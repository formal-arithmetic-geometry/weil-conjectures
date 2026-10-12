/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
import Sheaf.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-! # Flatness on a union of finite locally free loci

Source: blueprint lem-pc-perfect-locus, cohomology-sheaf gluing paragraph.
(blueprint: lem-pc-flat-restriction-union).
-/

@[expose] public section

set_option autoImplicit false
universe u v
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A module is flat on a union of opens where it is finite locally free.

Source: blueprint lem-pc-perfect-locus, cohomology-sheaf gluing paragraph; step 2
of lem-pc-derived-single-open-locus.
(blueprint: lem-pc-flat-restriction-union).

Proof: put W = the union of the U a. Each M restricted to U a is finite locally
free of some rank r a. Refine this cover by finite free trivializations. On each
trivializing open, tensoring with M is a finite direct sum of the identity,
hence preserves exact sequences. Tensor products commute with open restriction,
so the restriction of tensoring on W is tensoring with these finite free modules.
Exactness of a sequence of module sheaves can be checked on an open cover, or
on stalks. Thus tensoring with M restricted to W is exact, which is IsFlat.
Finite limits and colimits are preserved since this tensor functor is additive
between abelian categories and exact. No common rank or finite subcover is used.
For the empty family W is empty, the module category has only zero objects,
and every tensor functor is exact; rank-zero modules are also covered. -/
theorem isFlat_restrict_iSup_of_finiteLocallyFree
    {T : Scheme.{u}} (M : T.Modules) {ι : Type v} (U : ι → T.Opens)
    (hU : ∀ a, ∃ r : ℕ, ((restrictFunctor (U a).ι).obj M).IsFiniteLocallyFreeOfRank r) :
    SheafOfModules.IsFlat ((restrictFunctor (⨆ a, U a).ι).obj M) := by sorry

end AlgebraicGeometry.Scheme.Modules
