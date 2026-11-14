/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalEvaluationUnit
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerStrictAdjunctData
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerPureKernelNormalizationStatement
import WeilConjectures.AlgebraicGeometry.Kummer.KummerNormalizationComponents

/-! # Identification and normalization of the surviving Kummer cohomology -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance 11000] kummerModuleHasExt kummerAbHasExt
attribute [local irreducible] CategoryTheory.Abelian.Ext DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison cartierRootsIso
  cartierProKummerUnit cartierProRootMap diagonalFiniteToPadic diagonalForget
  diagonalScalarExtension diagonalScalarAdjunction

/-- Identify the surviving cohomology with roots, including its scalar action
and the unit equation, after a pure strict-system comparison has been supplied. -/
theorem strict_kummer_pure_kernel_normalization (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasExt.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (η : ∀ n, DiagonalEvaluationUnit (diagonalForget ℓ W)
      (diagonalScalarAdjunction ℓ W) D n) :
  strictKummerPureKernelNormalizationStatement ℓ W hW D η := by
  exact kummer_normalization_of_coefficients
    (A := DiagonalAb W) (B := DiagonalMod ℓ W)
    (abA := diagonalAbSheafAbelian W) (abB := diagonalModuleSheafAbelian _ W)
    (hA := kummerAbHasExt W)
    (catA := inferInstanceAs (Category (DiagonalAb W)))
    (catB := inferInstanceAs (Category (DiagonalMod ℓ W)))
    (hDerA := inferInstanceAs (HasDerivedCategory.{u + 1} (DiagonalAb W)))
    (hDerSys := inferInstanceAs (HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)))
    (hSys := inferInstanceAs (HasExt.{u + 1} (DiagonalSystems ℓ W)))
    (strictKummerNormalizationCoefficients ℓ W hW)
    ℓ (diagonalScalarExtension ℓ W) (diagonalScalarAdjunction ℓ W) D η
    (strict_kummer_kernel_triangles ℓ W hW)
    (strict_kummer_evaluation_triangles ℓ W hW D η)
    (strict_kummer_coefficient_lift ℓ W hW)

end AlgebraicGeometry.ProEtale
