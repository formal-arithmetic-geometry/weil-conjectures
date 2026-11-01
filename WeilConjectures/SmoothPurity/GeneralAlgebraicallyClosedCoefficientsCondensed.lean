/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-! The reanchored algebraically closed coefficient category.

This interface is the native bounded constructible category over the pulled-back
condensed algebraic closure. It contains no finite-stage pair category.
Source: det-def-sfb-bounded-constructible
(blueprint: def-weil-algebraically-closed-coefficients). -/

@[expose] public section
set_option autoImplicit false

universe u v

namespace WeilConjectures

/-- The condensed algebraically closed coefficient category.
Source: det-def-sfb-bounded-constructible
(blueprint: def-weil-algebraically-closed-coefficients). -/
noncomputable abbrev generalAlgebraicallyClosedConstructibleCategoryCondensed
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : AlgebraicGeometry.Scheme.{u}) :=
  AlgebraicGeometry.ProEtale.PadicAlgClConstructible Y l

end WeilConjectures
