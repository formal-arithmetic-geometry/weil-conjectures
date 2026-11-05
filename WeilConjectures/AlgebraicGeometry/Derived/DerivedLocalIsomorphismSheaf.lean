/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Derived.DerivedNormalizationArrowsSupplement
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # The sheaf of derived local isomorphisms

Source: Stacks Project, Tag 09BV, isomorphism sheaves, with the bounded-derived adaptation
of lem-weil-pbc-compatible-finite-derived-trivializations
(blueprint: def-weil-pbc-derived-local-isomorphism-sheaf).

The presheaf uses actual isomorphisms in the derived categories of the localized etale
sites, identified with the sites of the source schemes. Its restriction maps are the
canonical exact pullbacks, transported by their composition comparisons.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B]

variable {X B}

section RestrictionLaws

attribute [local irreducible] Etale.upperStar

end RestrictionLaws

section ProEtale

variable {Y : Scheme.{u}} (f : Y ⟶ X) {R S : Type (u + 1)} [CommRing R] [CommRing S]

end ProEtale

end AlgebraicGeometry.Scheme
