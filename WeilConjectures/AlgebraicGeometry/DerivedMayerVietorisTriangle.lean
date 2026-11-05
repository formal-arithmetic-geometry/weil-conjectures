/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisPresentation
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-! # Derived Mayer--Vietoris for a qcqs scheme

Source: Stacks Project, Cohomology, Tag 08BV; Derived Categories of Schemes, Tag 08D5
(blueprint: lem-pc-derived-mayer-vietoris-triangle).
-/

@[expose] public section

universe u₁ w₁

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048

end AlgebraicGeometry
