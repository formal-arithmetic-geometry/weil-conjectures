/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Boundary.FiniteBoundaryRestrictionUnderlying
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Local.DiagonalLocalFiniteConeChernClass

/-! Source endpoint transport for the finite Chern coordinate. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

/-- Source endpoint transport.  This is the coefficient-one calculation: the
finite quotient followed by the restricted evaluation comparison is the
integer coefficient map.  The proof is the coefficient-one section calculation,
additivity, and the constant-sheaf adjunction.
(blueprint: lem-diagonal-local-finite-source-endpoint-transport) -/
theorem finiteBoundary_source_endpoint
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [DiagonalTraceLocalizations l T]
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (k : Coefficients l (ULift.{u} (Padic l)) T c r) (n : ℕ) :
    let S := DerivedCategory.singleFunctor (DiagonalAb T) 0
    let e := finiteBoundaryRestrictionUnderlying l T r n
    S.map (finiteQuotient l (ULift.{u} (Padic l)) T n) ≫
        S.map (e.inv.app (coefficient T (Arings l (ULift.{u} (Padic l)) T))) =
      S.map (diagonalCoefficientIntegerMap T (Scheme.purTwistFiniteRing T l n) ≫
        k.coefficientForget.inv.app (op n)) := by
  sorry

end AlgebraicGeometry.ProEtale.DiagonalTrace
