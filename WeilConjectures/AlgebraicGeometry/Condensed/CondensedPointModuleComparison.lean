/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.Algebra.Category.Grp.AB

meta import Mathlib.Lean.Meta.CongrTheorems

/-!
# Module and derived comparison for pullback from the condensed point

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Section 3,
pp. 5--6, pullback paragraph before (3.1), Remark 3.2 and Definition 3.5
(blueprint: lem-zl-condensed-point-module-comparison).

The ordinary comparison is the existing `CondensedRing.upperStarFromPointModComp`.
Its scalar cancellation uses the specified coefficient isomorphism, and its underlying
map is `upperStarFromPointComp`. The internal module categories are identified with
sectionwise module sheaves by `InternalAbelianSheafModule.sectionModuleEquivalence`;
`InternalModuleOperations.upperComparison` identifies the two module inverse images.
All derived categories here are ordinary and unbounded.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory

end AlgebraicGeometry.ProEtale
