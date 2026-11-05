/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisExact
import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisComparisons

/-! # The short exact complex presenting direct-image Mayer--Vietoris

Source: Stacks Project, Cohomology, Tag 08BV, proof before passage to the triangle.
(blueprint: lem-pc-kinjective-mayer-vietoris-presentation).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

end AlgebraicGeometry
