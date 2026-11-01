/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import all WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientMapClosedGeometry
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import all WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The closed coefficient square under site-adjunction transport -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

local instance closed_site_pull_equivalence (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) [IsIso g] : (Sites.pull A g).IsEquivalence := by
  dsimp only [Sites.pull]
  infer_instance

local instance closed_site_proPull_equivalence (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) [IsIso g] : (Sites.proPull A g).IsEquivalence := by
  dsimp only [Sites.proPull]
  infer_instance

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  closedMap Sites.closedPull Sites.rnuScalar Sites.rnuPull
  Sites.proScalarPull Sites.sitePull Sites.scalarSite Sites.scalarPull

end WeilConjectures.FiniteFreeCoefficients
