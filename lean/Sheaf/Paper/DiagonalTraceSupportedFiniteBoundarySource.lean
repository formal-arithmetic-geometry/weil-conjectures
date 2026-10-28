/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DiagonalTraceSupportedSourceConeNormalization
public import Sheaf.Paper.DiagonalTraceFiniteCartierNormalization
public import Sheaf.Paper.DiagonalTraceSupportedFiniteBoundaryEquation

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
  completedSupportedUnit

/-- The projected supported strict class is the canonical finite Cartier arrow.
This assertion has no Chern normalization hypothesis: its endpoint is the reduced
Cartier class, not the Chern composite. The coordinates are normalized on one and
on roots, so the displayed endpoint cannot be chosen to fit the source composite.

Source: diagonal trace proof (2), source projection; diagonal-system proof (4).
(blueprint: lem-sfb-diagonal-trace-supported-finite-boundary-source-step).

Proof: compose k.coefficientForget with the canonical constant finite-ring
comparison to identify the evaluated coefficient unit with the constant residue
module. The residue-action equation of r makes this comparison linear, and
k.coefficient_one fixes its value on one. At level n take the source and root
isomorphisms sigma,t from hxi. Define the frame line isomorphism by e_n inverse
followed by t. FiniteRootNormalization and he give exactly a.line_roots.
Project the source-limit comparison at n using diagonalTower_limit. The equation
hs and the source normalization in hxi identify its integral generator with the
canonical positive finite quotient. completedSupportedUnit sends one to the
supported section one, so the resulting source map is the finite
constant-to-supported unit after the actual completed coefficient projection.
The l-regularity of the completed ring and its actual finite quotient identify
derived reduction of this unit with the finite constant unit; the reduction
adjunction extends the generator equation to the required derived source map.
Use hp to replace the presented arrow by xi, and the n-th finite-cycle equation
in hxi to replace its normalized evaluation by cartierResidueReducedPro.
The root normalization in hxi and he identify the target comparison with the
frame line coordinates. Finally the exact-cone projection equation identifies
the coefficient input for any L with its actual n-th projection. This proves the
stated supportedBoundaryEquation for arbitrary L₀ and L. The exponent is n+1,
so the same argument covers n=0; on the empty scheme all maps are unique. -/
theorem diagonalTrace_supportedFiniteBoundary_sourceStep
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalReductionPresentation l (diagonalScalarExtension l (diagonalSurface Y)))
    (H : DiagonalSystems l (diagonalSurface Y))
    (roots : H ⋙ diagonalForget l (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
    (xi : Ext (D.E.obj (diagonalIntegralSource Y)) H 2)
    (hxi : FiniteCartierNormalization l Y hY D H roots xi)
    (s : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (diagonalCompletedSource l Y) ≅ limit (D.E.obj (diagonalIntegralSource Y)))
    (hs : SupportedSourceConeNormalization l Y D s)
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (e : H ≅ r.F.obj (SpTowerClasses.lineModule l (ULift.{u} (Padic l)) c))
    (he : Functor.whiskerRight e.hom (diagonalForget l (diagonalSurface Y)) =
      roots.hom ≫ k.lineForget.inv)
    (p : ExtDerivedPresentation (D.E.obj (diagonalIntegralSource Y)) H)
    (hp : p.Presents xi)
    (L₀ L : DiagonalRlim (DiagonalMod l (diagonalSurface Y))) (n : ℕ) :
    ∃ a : SupportedFiniteBoundaryFrame l Y hY c r k n,
      supportedFiniteBoundaryCartierEquation l Y hY D H s c r k e p L₀ L n a := by
  sorry

end AlgebraicGeometry.ProEtale.DiagonalTrace
