/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisData
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisDegreewise

/-! # Exactness of the concrete direct-image Mayer--Vietoris complex

Source: Stacks Project, Cohomology, Tag 08BV, proof of Lemma 20.33.2,
using Tag 01EB and Tag 01EA.
(blueprint: lem-pc-kinjective-mayer-vietoris-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

end AlgebraicGeometry
