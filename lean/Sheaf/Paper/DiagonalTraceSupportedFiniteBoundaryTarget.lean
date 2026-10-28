/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DiagonalTraceSupportedFiniteBoundaryMaps

/-! # The finite Chern equation for a normalized strict supported Cartier class -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local instance] AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalConstantTowerLimits

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource diagonalCompletedCoefficientMap

attribute [local irreducible] CategoryTheory.Abelian.Ext
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison
  cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit cartierReducedEtale
  cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierProIntegralGenerator cartierProRootMap cartierResidueReducedPro
  diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary
  diagonalSingleLimitComparison diagonalExactFunctorExtImage
  diagonalShiftedSingleLimitComparison diagonalCompletedGenerator
  SpTowerClasses.lineModule Coefficients.unitMap

/-- A finite class satisfying the geometric Kummer Chern equation gives the
normalized coefficient Chern arrow. This contains no strict class, source cone,
or presentation. It applies to any finite Cartier class with the stated equation.

Source: diagonal trace proof (2), coefficient comparison; classes proof (3).
(blueprint: lem-sfb-diagonal-trace-supported-finite-boundary-target-step).

Proof: apply hc at diagonalPic Y and n. The normalization hn identifies its
boundary with the positive Kummer boundary and identifies its scalar comparisons
with the ordinary ones. Unpack hz to obtain the ordinary etale Chern class whose
integral adjunct is supportedKummerChern and whose comparison pullback is the
constant-to-support composite of z. The coefficient-one and root-tensor equations
of k, together with a.coefficient_one and a.line_roots, identify the quotient and
root maps in hc with these same finite maps. The Cartier divisor line in this
calculation is the dual diagonal ideal, hence diagonalPic Y. Apply the integral
to finite scalar-unit Ext bijection to identify the coefficient-linear finite
arrows from their equal integral adjuncts. Transport through the exact single,
shift, evaluation and scalar-restriction comparisons defining the frame maps.
Precompose the coefficient cone projection; the exact-cone projection identity
identifies this with k.unitMap followed by L.projection n. This gives the asserted
equality. No choice of a strict Cartier representative occurs. The argument
works at positive exponent n+1, including n=0 and the empty scheme. -/
theorem diagonalTrace_supportedFiniteBoundary_targetStep
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (hn : c.Normalized l (ULift.{u} (Padic l)))
    (hc : SpTowerClasses.FiniteChernNormalization l (ULift.{u} (Padic l)) c)
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (n : ℕ) (a : SupportedFiniteBoundaryFrame l Y hY c r k n)
    (L : DiagonalRlim (DiagonalMod l (diagonalSurface Y)))
    (z : GeoCartierClass (diagonalResidue.{u} l n) (l ^ (n + 1))
      (cartierResidue_cast l (n + 1)) (diagonalImmersion Y))
    (hz : GeoCartierChernEquation (diagonalResidue.{u} l n) (l ^ (n + 1))
      (cartierResidue_cast l (n + 1)) (diagonalImmersion Y)
      (diagonalImmersion_cartier Y) (diagonalSurface_power_unit l Y hY n) z) :
    a.cartierMap l Y hY c r k n L z =
      finiteChernComposite l (diagonalSurface Y) c r k L n
        (SpTowerClasses.diagonalPic Y) := by
  sorry

end AlgebraicGeometry.ProEtale.DiagonalTrace
