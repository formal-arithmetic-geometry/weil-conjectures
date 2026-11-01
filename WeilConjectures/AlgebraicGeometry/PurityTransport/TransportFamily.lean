/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportGeometry

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-adjunction-family). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- A family indexed only by smooth separated finite-type morphisms over the
fixed field. Source: smooth purity (blueprint: def-pur-transport-adjunction-family). -/
abbrev AdjunctionFamily (D : WeilConjectures.FiniteFieldDatum.{u}) :=
  ∀ (c : Coefficient ell) (s : SmoothDatum D), ExplicitAdjunction ell D c s

end AlgebraicGeometry.ProEtale.PurityTransport
