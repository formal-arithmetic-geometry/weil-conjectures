/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleResolutionCocycleEquivalences
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleResolutionCocycleCompatibility

/-! # Cocycle comparisons for object cohomology

Source: Stacks Project, Cohomology on Sites, Section 01FT;
Derived Categories, Tag 06XR (1).
(blueprint: lem-weil-pbc-zariski-etale-resolution-cocycle-homology)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

