/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport

/-!
# Constructible cohomological intervals

Source: Weil blueprint, order 1466 (blueprint: def-weil-constructible-intervals).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The full constructible interval, with vanishing outside the inclusive integer interval.
When b < a the interval is empty, so all cohomology vanishes.
Source: Weil blueprint, order 1466 (blueprint: def-weil-constructible-intervals). -/
noncomputable def constructibleInterval (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (Y : AlgebraicGeometry.Scheme.{u}) (a b : ℤ) :
    ObjectProperty (proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)) :=
  intrinsicFiniteTorsionConstructible l E n hn Y ⊓
    fun K ↦ proEtaleCohomologicalSupport K ⊆ Set.Icc a b

/-- The inherited full subcategory; no change of morphisms or triangulated completion.
Source: Weil blueprint, order 1466 (blueprint: def-weil-constructible-intervals). -/
noncomputable abbrev constructibleIntervalCategory (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (Y : AlgebraicGeometry.Scheme.{u}) (a b : ℤ) :=
  (constructibleInterval l E n hn Y a b).FullSubcategory

end WeilConjectures
