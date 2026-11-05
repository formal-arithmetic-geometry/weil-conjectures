/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Bounded flat models of complexes of modules of finite Tor amplitude

Source: Stacks Project, More on Algebra, Lemma 15.59.3 (Tag 0654)
(blueprint: lem-pc-module-tor-amplitude-flat-model).
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

-- The fixed interface includes `hab`; the generic equivalence needs no interval ordering.

end DerivedCategory
