/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Explicit étale-origin witnesses

Source: Weil conjectures blueprint, proper base change,
`def-weil-pbc-etale-origin-witness`, order 1289
(blueprint: def-weil-pbc-etale-origin-witness).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- An explicit bounded-below étale origin for a pro-étale derived object.  The source
retains the étale complex and its comparison isomorphism as data, rather than merely
asserting that such data exists. Source: Weil conjectures blueprint,
`def-weil-pbc-etale-origin-witness` (blueprint: def-weil-pbc-etale-origin-witness). -/
structure EtaleOriginWitness (T : Scheme.{u}) (Λ : Type (u + 1))
    [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (K : FiniteCoefficientDerivedCategoryPlus T Λ) where
  /-- The bounded-below étale derived object furnishing the origin. -/
  L : DerivedCategory.Plus
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  /-- The specified comparison isomorphism from the étale origin to `K`. -/
  alpha : (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus.obj L ≅ K

end AlgebraicGeometry.ProEtale
