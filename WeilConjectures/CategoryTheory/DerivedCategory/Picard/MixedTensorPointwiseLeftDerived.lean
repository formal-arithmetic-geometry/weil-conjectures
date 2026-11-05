/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.MixedTotalTensor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.MixedTensorKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Exact left derived mixed tensor for a fixed complex

Source: Stacks Project, More on Algebra, Section 06Y5, Tag 06Y6.
(blueprint: lem-pc-mixed-tensor-pointwise-left-derived)
-/

@[expose] public section

set_option synthInstance.maxSize 512

universe u wR wA

open CategoryTheory CategoryTheory.Functor

namespace DerivedCategory

end DerivedCategory
