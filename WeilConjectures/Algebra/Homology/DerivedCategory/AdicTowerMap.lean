/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Exact linear functors preserve normalized adic towers

Let `F : 𝒜 ⥤ ℬ` be an exact `R`-linear functor between `R`-linear abelian categories. Applying
`F` termwise to a normalized `ϖ`-adic tower of cochain complexes
(`CochainComplex.IsNormalizedAdicTower`) gives a normalized `ϖ`-adic tower:
`CochainComplex.IsNormalizedAdicTower.map`.
-/

@[expose] public section

open CategoryTheory Category Limits Opposite

namespace CochainComplex.IsNormalizedAdicTower

variable {R : Type*} [Ring R] {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] [Abelian 𝒜] [Abelian ℬ]
  [Linear R 𝒜] [Linear R ℬ] (F : 𝒜 ⥤ ℬ) [F.Additive] [F.Linear R] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]

end CochainComplex.IsNormalizedAdicTower
