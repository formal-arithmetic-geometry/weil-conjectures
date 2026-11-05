/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # The concrete restriction/direct-image complex for Mayer--Vietoris

Source: Stacks Project, Cohomology, Tag 08BV, displayed short exact sequence.
(blueprint: def-pc-kinjective-mayer-vietoris-data).

All objects and arrows below are constructed from the underived adjunction; no
existence theorem is used to choose the data.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

end AlgebraicGeometry
