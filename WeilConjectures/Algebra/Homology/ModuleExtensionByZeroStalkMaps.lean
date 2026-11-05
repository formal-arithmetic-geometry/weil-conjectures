/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkOutside
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkInside
import WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkTransitions
public import Mathlib.Topology.Sheaves.Module

/-! # Stalks and maps for extension by zero of modules

Source: literature/stacks-project/sheaves.tex, Tag 00A7, clauses (2)--(4),
and the presheaf construction preceding it.
(blueprint: lem-sc-module-extension-by-zero-stalk-maps)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

noncomputable section

namespace AlgebraicGeometry

end AlgebraicGeometry
