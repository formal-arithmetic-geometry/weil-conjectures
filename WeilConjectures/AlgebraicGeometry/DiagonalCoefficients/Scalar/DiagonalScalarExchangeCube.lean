/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackComparison
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientScalars

/-! # Scalar extension and the normalized model exchange cube -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

variable {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
  (a : R ⟶ T) [IsMonHom a]

/-- Scalar extension commutes with the normalized geometric exchange mate.
This is an equality of comparisons on arbitrary derived objects and contains
no trace, invertibility assertion, or line endpoint. -/
theorem scalar_model_exchange_cube
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f)
    (D₀ : DiagonalRightDerived (CondensedRing.lowerStar R f))
    (D₀' : DiagonalRightDerived (CondensedRing.lowerStar R f'))
    (D : DiagonalRightDerived (CondensedRing.lowerStar T f))
    (D' : DiagonalRightDerived (CondensedRing.lowerStar T f'))
    (e₀ : D₀.R = derivedLower R f) (e₀' : D₀'.R = derivedLower R f')
    (e : D.R = derivedLower T f) (e' : D'.R = derivedLower T f')
    (he₀ : IsCanonicalRightDerived (CondensedRing.lowerStar R f) D₀ e₀)
    (he₀' : IsCanonicalRightDerived (CondensedRing.lowerStar R f') D₀' e₀')
    (he : IsCanonicalRightDerived (CondensedRing.lowerStar T f) D e)
    (he' : IsCanonicalRightDerived (CondensedRing.lowerStar T f') D' e')
    (r : RestrictionSquare a f D₀ D) (r' : RestrictionSquare a f' D₀' D')
    (K : DerivedCategory (Modules R X)) :
    (scalarPullbackComparison a hS).app (D₀.R.obj K) ≫
        (derivedUpper T hS).map ((r.mate a).app K) ≫
        modelExchange T f f' hX hS h D D' e e' ((derivedScalars a X).obj K) =
      (derivedScalars a S').map (modelExchange R f f' hX hS h D₀ D₀' e₀ e₀' K) ≫
        (r'.mate a).app ((derivedUpper R hX).obj K) ≫
        D'.R.map ((scalarPullbackComparison a hX).app K) := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
