/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import Mathlib.CategoryTheory.Generator.Basic

/-!
# Grothendieck abelianness of constant-coefficient etale module sheaves

Source: Stacks Project, Modules on Sites, Tags 03DA, 03DB, 03DI and 03EW;
Topologies, Tags 021A, 021B and 04HR
(blueprint: lem-weil-pbc-module-sheaves-grothendieck-abelian).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
