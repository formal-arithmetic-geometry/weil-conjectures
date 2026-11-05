/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.Etale.Derived.HeartGluing
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Comparison of extension by zero on the etale and pro-etale sites

Source: Stacks Project, Tag 09AF (`lemma-jshriek-comparison`); Weil conjectures
blueprint, `sec-smooth-purity/sk-prop-sf-cbc`
(blueprint: lem-cbc-proetale-extension-zero-comparison).

The comparison is the existing adjunction mate
`openImmersionLowerShriekComparisonUpperStarIso`, not a chosen isomorphism.
-/

@[expose] public section

universe u' u

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory

-- Transport adjunctions along the specified restriction isomorphisms.

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme CategoryTheory.Limits Opposite
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
variable {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
  [IsOpenImmersion k] [IsOpenImmersion j]

-- Literal restriction composition, before transporting to the chosen pullbacks.
-- The public extension composition maps are mates of literal restriction composition.

-- Identity restriction and its compatibility with the canonical pullback unit.

end AlgebraicGeometry.ProEtale
