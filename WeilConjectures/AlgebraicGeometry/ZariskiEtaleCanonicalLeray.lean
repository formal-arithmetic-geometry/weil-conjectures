/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.ZariskiEtalePushedResolution
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleResolutionMap
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Canonical Leray comparison for the Zariski-to-étale morphism

Source: Stacks Project, Cohomology on Sites, Tags 072W and 0733(1).
(blueprint: lem-weil-pbc-zariski-etale-canonical-leray)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction

