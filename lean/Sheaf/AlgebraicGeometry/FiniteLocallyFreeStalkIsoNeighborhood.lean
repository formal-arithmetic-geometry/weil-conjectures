/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # A stalk inverse extends to a vector bundle neighbourhood

Source: Stacks Project, Tags 05GF and 00O0, Lemmas 10.79.2 and 10.79.4(3).
(blueprint: lem-sc-finite-locally-free-stalk-iso-neighborhood)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- A finite locally free map invertible at one stalk is invertible on an open
neighbourhood of that point.
Source: Stacks Project, Tags 05GF and 00O0, Lemmas 10.79.2 and 10.79.4(3).
(blueprint: lem-sc-finite-locally-free-stalk-iso-neighborhood)

Proof: Intersect finite free trivializing neighbourhoods for M and N at x. In
these frames φ is a finite rectangular matrix of sections. Its stalk inverse
is a finite matrix of germs. Represent its finitely many entries by sections
and intersect their domains with the trivializing neighbourhood. The identities
AB = 1 and BA = 1 hold as germs. There are finitely many entries in the two
matrix identities; for each entry the germ equality criterion supplies a smaller
neighbourhood where the equality holds. Intersect all of them. The resulting
matrix of sections defines a morphism N to M on that open, and the two matrix
identities give a two-sided inverse to the restricted map. For an open immersion,
the restriction functor is naturally isomorphic to tensor pullback: both are
left adjoints of the same pushforward. Naturality transports the inverse to the
map written here. Zero ranks cause no difficulty: the corresponding finite
families and identity matrices are empty. No noetherian hypothesis is needed. -/
theorem exists_isIso_tensorPullback_of_isIso_moduleStalkMap
    {W : Scheme.{u}} (M N : W.Modules)
    [M.IsFiniteLocallyFree] [N.IsFiniteLocallyFree] (φ : M ⟶ N) (x : W)
    (hφ : IsIso ((RingedSpace.moduleStalkFunctor W.toRingedSpace x).map φ)) :
    ∃ U : W.Opens, x ∈ U ∧ IsIso ((tensorPullback U.ι).map φ) := by sorry

end AlgebraicGeometry.Scheme.Modules
