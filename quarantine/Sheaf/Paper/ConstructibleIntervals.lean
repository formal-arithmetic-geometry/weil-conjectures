/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Constructible cohomological intervals

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-def-sf-operations`,
`def-weil-constructible-intervals`, order 1466
(blueprint: def-weil-constructible-intervals).

The object predicate combines intrinsic finite-torsion bounded constructibility with
vanishing of cohomology outside the inclusive integer interval. Its full subcategory
has exactly the inherited morphisms, identities and composition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Membership in the constructible interval `[a,b]`: intrinsic bounded constructibility
and vanishing of every cohomology sheaf in a degree outside `Set.Icc a b`.
The coefficient ring is the recorded quotient `𝒪_E / ϖ_Eⁿ 𝒪_E`. Invertibility of `l`
on `Y` is expressed in every local ring of `Y`.
Source: Weil blueprint, `def-weil-constructible-intervals`, order 1466
(blueprint: def-weil-constructible-intervals). -/
noncomputable def finiteTorsionConstructibleIn
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u})
    (_hl : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) (a b : ℤ) (_hab : a ≤ b) :
    ObjectProperty (proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)) :=
  intrinsicFiniteTorsionConstructible l E n hn Y ⊓ fun K ↦
    ∀ r : ℤ, r ∉ Set.Icc a b →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y
          (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))) r).obj K)

/-- The full subcategory `D_c^[a,b](Y,A_{E,n})` on bounded constructible objects with
cohomology vanishing outside the inclusive interval `[a,b]`. The full-subcategory
construction inherits every ambient morphism and its identities and composition;
these are also exactly the morphisms of the bounded constructible full subcategory.
Source: Weil blueprint, `def-weil-constructible-intervals`, order 1466
(blueprint: def-weil-constructible-intervals). -/
noncomputable abbrev finiteTorsionConstructibleIntervalCategory
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u})
    (hl : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) (a b : ℤ) (hab : a ≤ b) :=
  (finiteTorsionConstructibleIn l E n hn Y hl a b hab).FullSubcategory

end AlgebraicGeometry.Scheme
