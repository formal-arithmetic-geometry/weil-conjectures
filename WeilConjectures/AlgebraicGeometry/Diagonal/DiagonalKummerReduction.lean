/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSourceQuotientNormalization
import WeilConjectures.AlgebraicGeometry.SixFunctors.SheafKummerTransportAssembly
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalFiniteCartierNormalization

/-! # Kummer calculation of the simultaneously reduced Cartier boundary -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] CategoryTheory.Abelian.Ext
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance 11000] kummerModuleHasExt kummerAbHasExt

attribute [local irreducible] normalizedBoundaryTarget DiagonalSourceNormalization
  DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ diagonalDerivedSingleCounit
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison cartierRootsIso
  cartierEtaleKummerUnit cartierProKummerUnit cartierProIntegralGenerator cartierProRootMap
  cartierReducedEtale cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierResidueReducedPro diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary

/-- Once the source counit is invertible, Kummer reduction identifies the target
and the evaluated reduced boundary with the normalized finite Cartier classes.

Source: Stacks Tags 03PL, 0152 and 06YY. -/
theorem diagonal_kummer_reduction (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (ha : a.hom = diagonalDerivedSingleCounit ℓ
      (diagonalScalarExtension ℓ (diagonalSurface Y)) D (diagonalIntegralSource Y)) :
    diagonalBoundaryTarget ℓ Y hY D a := by
  have hW : IsUnit (ℓ : Γ(diagonalSurface Y, ⊤)) := by
    simpa only [Nat.zero_add, Nat.pow_one] using diagonalSurface_power_unit ℓ Y hY 0
  unfold diagonalBoundaryTarget
  refine sheaf_kummer_transport_assembly ℓ (diagonalSurface Y) hW D
    (diagonalIntegralSource Y)
    (fun n => (lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))
      (diagonalImmersion Y)).obj
        (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y)))
    (fun n => cartierProIntegralGenerator (diagonalResidue.{u} ℓ n) (diagonalImmersion Y))
    (diagonalIntegralBoundary Y) a ha ?_ ?_ ?_
  · exact fun n => diagonal_source_quotient_normalization ℓ Y D.ordinary n
  · intro n s hs
    unfold DiagonalSourceNormalization at hs
    exact hs
  · exact fun n e he => diagonal_finite_cartier_normalization ℓ Y hY hW n e he

end AlgebraicGeometry.ProEtale
