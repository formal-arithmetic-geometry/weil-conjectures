/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientSourcePullback

/-! # Completed diagonal class under geometric inverse image
-/

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

/-- Geometric inverse image of the completed positive diagonal class, before any
trace or extension of coefficients is considered. The supported source comparison
and the positive-line endpoint are normalized on ordinary sheaves. -/
theorem diagonalCompletedClass_pullback (l : ℕ) [Fact l.Prime]
    (Y Y' : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y')]
    (g : Y' ⟶ Y) (geometry : BaseSquares g)
    (hY : IsUnit (l : Γ(Y, ⊤))) (hY' : IsUnit (l : Γ(Y', ⊤)))
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y')))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (δ' : diagonalCompletedDomain l Y' ⟶ diagonalCompletedCodomain l Y')
    (hdelta : DiagonalTrace.IsDiagonalLimit l Y hY D δ)
    (hdelta' : DiagonalTrace.IsDiagonalLimit l Y' hY' D' δ')
    (eP : CompletedRealization l (ProjectiveLine Y))
    (eW : CompletedRealization l (diagonalSurface Y))
    (eP' : CompletedRealization l (ProjectiveLine Y'))
    (eW' : CompletedRealization l (diagonalSurface Y'))
    (s : eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : eW'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y')
    (hs : HEq (eW.underlying.inv.app (diagonalCompletedSource l Y) ≫ s.hom.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (eP.underlying.inv.app (SheafOfModules.unit
          (Scheme.purTwistRing (ProjectiveLine Y)
            (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≫ eP.unitIso.hom.hom)))
    (hs' : HEq (eW'.underlying.inv.app (diagonalCompletedSource l Y') ≫ s'.hom.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y')).map
        (eP'.underlying.inv.app (SheafOfModules.unit
          (Scheme.purTwistRing (ProjectiveLine Y')
            (Scheme.purTwistZlCompletion (ProjectiveLine Y') l))) ≫ eP'.unitIso.hom.hom))) :
    let R := Profinite.continuousMapRingObj.{u} ℤ_[l]
    let δz := (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).map s.inv ≫
      SpTowerClasses.mapSingleArrow eW.F (2 : ℤ) δ ≫
        ((DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).map
          eW.lineIso.hom)⟦(2 : ℤ)⟧'
    let δz' := (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map s'.inv ≫
      SpTowerClasses.mapSingleArrow eW'.F (2 : ℤ) δ' ≫
        ((DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map
          eW'.lineIso.hom)⟦(2 : ℤ)⟧'
    ∃ data : SourcePullback R g (zlLine l)
        (spIntegralComparison (baseP g) l (bottomField l))
        (spIntegralComparison (baseW g) l (bottomField l)),
      (derivedUpper R (baseW g)).map δz ≫ data.endpoints.lineW.shift =
        (singlePullback R (baseW g) (source R Y)).hom ≫
          (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map
            data.supported.hom ≫ δz' := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
