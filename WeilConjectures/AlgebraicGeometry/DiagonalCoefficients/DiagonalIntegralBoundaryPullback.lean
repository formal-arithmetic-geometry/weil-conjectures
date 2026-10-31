/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierPoleBoundaryPullback
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Pullback of the positive integral diagonal boundary

Source: the latest blueprint, diagonal coefficient changes, paragraph (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] CategoryTheory.Abelian.Ext Ext.comp Ext.mapExactFunctor
  diagonalIntegralBoundary cartierIntegralSourceIso

/-- The supported integral endpoint obtained by transporting the canonical etale
closed exchange through the two fixed site comparisons.
Source: blueprint coefficient proof (3), Cartier extension pullback
(blueprint: lem-diagonal-integral-boundary-pullback). -/
def diagonalBoundarySource {Y Y' : Scheme.{u}}
    (v : diagonalSurface Y' ⟶ diagonalSurface Y)
    (w : ProjectiveLine Y' ⟶ ProjectiveLine Y)
    (sq : CommSq w (diagonalImmersion Y') (diagonalImmersion Y) v) :
    (upperStar Ab.{u + 1} v).obj (diagonalIntegralSource Y) ⟶
      diagonalIntegralSource Y' :=
  (upperStar Ab.{u + 1} v).map (cartierIntegralSourceIso (diagonalImmersion Y)).inv ≫
    (comparisonUpperStarCompUpperStarIso Ab.{u + 1} v).hom.app _ ≫
    (comparisonUpperStar Ab.{u + 1} (diagonalSurface Y')).map
      (Etale.relativeExtensionExchange (diagonalImmersion Y) (diagonalImmersion Y') v w sq) ≫
    (cartierIntegralSourceIso (diagonalImmersion Y')).hom

/-- The units endpoint is the canonical units pullback through the comparison square.
Source: blueprint coefficient proof (3), units map
(blueprint: lem-diagonal-integral-boundary-pullback). -/
def diagonalBoundaryUnits {Y Y' : Scheme.{u}}
    (v : diagonalSurface Y' ⟶ diagonalSurface Y) :
    (upperStar Ab.{u + 1} v).obj (diagonalComparisonUnits Y) ⟶
      diagonalComparisonUnits Y' :=
  (comparisonUpperStarCompUpperStarIso Ab.{u + 1} v).hom.app _ ≫
    (comparisonUpperStar Ab.{u + 1} (diagonalSurface Y')).map
      (Scheme.upperStarGmSheafToGmSheaf v)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
