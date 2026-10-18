/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.Paper.ConstructibleIntervalsUnordered

/-!
# Intrinsic finite-coefficient constructible intervals

Source: blueprint master, sec-smooth-purity/sk-def-sf-operations, order 1466
(blueprint: def-weil-constructible-intervals).

The recorded fixed-scalar `constructibleIn` has a different ambient category. This module
reexports the existing intrinsic `constructibleIntervalCategory` without constructing
a second interval category. No comparison or etale-origin hypothesis is introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The finite constructible interval full subcategory in the intrinsic presentation.
Its objects are bounded constructible objects with every cohomology sheaf outside `[a,b]`
zero. The formula is defined for any bounds and used for `a ≤ b`. Morphisms, identities
and composition are inherited from the ambient derived category. This is a transparent
alias of the existing `constructibleIntervalCategory`, whose predicate intersects intrinsic
constructibility with cohomological support contained in the inclusive interval.
Source: blueprint order 1466 (blueprint: def-weil-constructible-intervals). -/
abbrev intrinsicConstructibleIntervalCategory
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (T : AlgebraicGeometry.Scheme.{u}) (a b : ℤ) :=
  constructibleIntervalCategory l E n hn T a b

end WeilConjectures
