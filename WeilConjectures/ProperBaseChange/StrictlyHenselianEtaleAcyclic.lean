/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Etale acyclicity of a strictly henselian local scheme

Source: Stacks Project, etale-cohomology.tex, Lemma Tag 03QO
(blueprint: lem-weil-pbc-strictly-henselian-etale-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

