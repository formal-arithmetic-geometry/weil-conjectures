/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Power torsion of Hom from a bounded finite-projective complex

Source: Stacks Project, Tag 08EJ, affine paragraph.
(blueprint: lem-sc-bounded-projective-hom-power-torsion).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace DerivedCategory

end DerivedCategory
