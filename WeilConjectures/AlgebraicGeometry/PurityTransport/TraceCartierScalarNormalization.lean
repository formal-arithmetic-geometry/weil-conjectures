/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceCartierBoundaryExistence
import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceCartierScalarCoordinates
import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceCartierScalarEquation

/-! # Scalar normalization of the native Cartier boundary

This is the scalar-transport part of native Cartier existence.
(blueprint: new-det-sp-trace-cartier-scalar-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport.TraceCartierBoundaryData
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- A boundary-realized family satisfies the native scalar equation.  Derived
associativity transports the entire integral pole extension and Kummer boundary
through a coefficient map, while the degree-zero unit component is the
normalized `traceScalarUnit`.  The supported-source component is the direct
image scalar mate.  Adjunction-unit and tensor-associativity identities show
that these are the same comparison, including nonflat maps, empty supports,
and zero coefficient rings.
Source: `sk-def-sp-trace-properties.proof.md`, (2), scalar-transport paragraph
 (blueprint: new-det-sp-trace-cartier-scalar-normalization). -/
theorem traceCartier_scalar_of_boundary
    (C : TraceCartierFamily.{u} ell)
    (hC : TraceCartierBoundary ell C) :
    TraceCartierScalar ell C := by
  intro c c' a ha Z T i _ hI hT
  obtain ⟨pZ⟩ := trace_scalar_coordinates_nonempty ell a ha Z
  obtain ⟨pT⟩ := trace_scalar_coordinates_nonempty ell a ha T
  exact ⟨pZ, pT, traceCartier_scalar_equation_of_boundary ell C hC a ha i hI hT pZ pT⟩

end AlgebraicGeometry.ProEtale.PurityTransport
