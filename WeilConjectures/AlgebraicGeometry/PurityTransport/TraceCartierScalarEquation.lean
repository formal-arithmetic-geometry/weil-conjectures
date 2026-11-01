/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceCartierBoundaryExistence
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceCartierScalarCoordinates
import WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerBoundaryScalar
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.ScalarBoundaryComparison

/-! # Scalar square for a boundary-realized Cartier family

The coordinate witnesses are constructed independently.  This node isolates the
remaining derived scalar-mate equation.
(blueprint: new-det-sp-trace-cartier-scalar-equation).
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

/-- Once normalized scalar coordinates are fixed, a boundary-realized family
satisfies the displayed scalar square.  The proof transports the full integral
pole extension and Kummer boundary through the derived scalar mate; adjunction
unit and tensor associativity identify the two resulting composites.  This is
strictly the equation part of `TraceCartierScalar`, with its two coordinates
provided as inputs.
Source: `sk-def-sp-trace-properties.proof.md`, (2), scalar-transport paragraph
(blueprint: new-det-sp-trace-cartier-scalar-equation). -/
theorem traceCartier_scalar_equation_of_boundary
    (C : TraceCartierFamily.{u} ell)
    (hC : TraceCartierBoundary ell C)
    {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell)
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (ell : Γ(T, ⊤)))
    (pZ : ScalarLineCoordinates ell a ha Z)
    (pT : ScalarLineCoordinates ell a ha T) :
    (scalarSixChange a T).map (C c i hI hT) ≫
        scalarLineMap ell a T 1 (pT.power 1) =
      (scalarDirectMate a i).app (unit ell c Z) ≫
        (actualPush (c'.obj.{u} ell) i).map (traceScalarUnit ell a ha Z pZ) ≫
          C c' i hI hT := by
  sorry

end AlgebraicGeometry.ProEtale.PurityTransport
