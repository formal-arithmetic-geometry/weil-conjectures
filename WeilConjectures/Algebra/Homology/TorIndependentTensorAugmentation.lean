/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.Algebra.Homology.TorIndependentScalarAugmentation
import WeilConjectures.Algebra.Homology.MixedTensorRestrictionComparison
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided

/-! # Tor independence and tensor augmentation

Source: Stacks Project, Tags 06Y6 and 08IB.
(blueprint: lem-pc-tor-independent-tensor-augmentation).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace ModuleCat

end ModuleCat
