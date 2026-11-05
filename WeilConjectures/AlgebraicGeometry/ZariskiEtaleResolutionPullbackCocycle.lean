/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
import WeilConjectures.AlgebraicGeometry.ZariskiEtalePullbackMapExt
import WeilConjectures.CategoryTheory.ExactFunctorResolutionCocycle

/-! # Cocycle comparisons for object cohomology

Source: Stacks Project, Cohomology, Tags 01F8 and 01FB;
Derived Categories, Tags 013P and 015B (4).
(blueprint: lem-weil-pbc-zariski-etale-resolution-pullback-cocycle)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction

