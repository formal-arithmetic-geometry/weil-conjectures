/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimitExtension

/-!
# Extending acyclic constant coefficients from cyclic groups to torsion groups

Source: Stacks Project, Tag 0GJR, proof of lemma-locally-acyclic-locally-constant.
(blueprint: lem-weil-pbc-constant-torsion-acyclic-devissage).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
