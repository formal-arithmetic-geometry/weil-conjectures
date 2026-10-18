/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules

/-!
# Bounded below derived pullback from the etale site

Source: Stacks Project, Tags 015F and 099R, comparison inverse image applied termwise
(blueprint: def-sf-comparison-derived-pullback).

The unbounded functor is the existing `finiteCoefficientDerivedComparison`. The
bounded below functor below uses the same exact module inverse image, including its
canonical realization as modules over the continuous-function coefficient ring sheaf.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The comparison inverse image on bounded below derived categories: apply the exact
module inverse image termwise and restrict its induced localization functor to the
standard bounded below subcategories. Its unbounded version is the existing
`finiteCoefficientDerivedComparison`, and `Functor.mapDerivedCategoryPlusCompatibility`
identifies the restriction with that version after inclusion. Exactness implies that
cohomology commutes with inverse image, so the same lower bound is retained.
Source: Stacks Project, Tag 015F and Tag 099R, proof of the relative comparison lemma
(blueprint: def-sf-comparison-derived-pullback). -/
noncomputable abbrev finiteCoefficientDerivedComparisonPlus (T : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] :
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      FiniteCoefficientDerivedCategoryPlus T Λ :=
  (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus

end AlgebraicGeometry.ProEtale
