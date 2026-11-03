/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralPurityTransport.CanonicalAdjunctionConstruction

/-! # The canonical constructed smooth adjunction family

Source: the construction preceding (10.1), transport proof Steps 1--4.
(blueprint: def-pur-general-construction-family).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.GeneralPurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- The normalized family determined uniquely by the construction theorem.
Source: the construction preceding (10.1)
(blueprint: def-pur-general-construction-family). -/
def constructionFamily (k : Type u) [Field k]
    [Fact (ringChar k).Prime] (hk : Finite k ∨ IsAlgClosed k)
    (hEll : IsUnit (ell : k)) : AdjunctionFamily ell k :=
  (existsUnique_constructionFamily ell k hk hEll).exists.choose

end AlgebraicGeometry.ProEtale.GeneralPurityTransport
