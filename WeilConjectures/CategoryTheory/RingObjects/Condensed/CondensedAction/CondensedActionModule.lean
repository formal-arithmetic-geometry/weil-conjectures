/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import WeilConjectures.CategoryTheory.CondensedActionModule

/-! # Internal modules with an action of a profinite condensed group

Source: blueprint, direct-image stability, paragraph (3), internal-action categorical input
(blueprint: def-sfb-condensed-action-module).

The underlying object is the recorded internal module object. Its section module is read
through the existing section-module equivalence. Actions use all continuous maps from a
profinite test object and commute with restriction; they are not abstract group actions.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite.CondensedAction

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

variable (P : Type u) [TopologicalSpace P] [Group P] [IsTopologicalGroup P]

variable {R P}

variable {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]

variable (R P)

variable (G H : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  [TopologicalSpace H] [Group H] [IsTopologicalGroup H]

end Profinite.CondensedAction
