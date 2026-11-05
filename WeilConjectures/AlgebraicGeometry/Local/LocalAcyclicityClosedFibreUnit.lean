/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityAbelianSheaf
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityClosedFibreStalks
import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityClosedFibreUnitGerm
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Local acyclicity and the closed-fibre restriction of the derived unit

Source: Stacks Project, Tag 0GJU, lemma-beta-is-isomorphism, specialized to `G[0]`
(blueprint: lem-weil-pbc-local-acyclicity-closed-fibre-unit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
