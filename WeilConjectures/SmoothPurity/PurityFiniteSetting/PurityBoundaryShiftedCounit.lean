/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityBoundaryComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructureStatement

/-! # Shifted closed counits in exact direct-image coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

/-- The specified comparison from the exceptional value of the shifted input to
its shifted exceptional value. It is the composite-functor shift comparison, followed
by the bounded-below inclusion comparison used in gysinSupportToHom.
Source: lem-pur-gysin-structure.proof.md, supported-Hom paragraph.
(blueprint: def-pur-boundary-shifted-counit). -/
def boundaryAdjunctShift (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :
    (sfFiniteExceptionalFixed P.Ring (Compactification.ofIsProper (zeroSection Y))).obj
        ((P.gysinInput h Y).obj⟦(2 : ℤ)⟧) ⟶ P.gysinValue h Y := by
  let s := zeroSection Y
  letI := (Compactification.ofIsProper s).hasCompactification
  exact
    ((comparisonUpperStar (Modules P) Y).mapDerivedCategory.map
      ((Etale.rightDerivedUpperShriek P.Coefficient s).map
        (((comparisonLowerStar (Modules P) (Line Y)).rightDerivedFunctor.commShiftIso
          (2 : ℤ)).hom.app (P.gysinInput h Y).obj) ≫
        ((Etale.rightDerivedUpperShriek P.Coefficient s).commShiftIso (2 : ℤ)).hom.app
          ((comparisonLowerStar (Modules P) (Line Y)).rightDerivedFunctor.obj
            (P.gysinInput h Y).obj)) ≫
      ((comparisonUpperStar (Modules P) Y).mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((Etale.rightDerivedUpperShriek P.Coefficient s).obj
          ((comparisonLowerStar (Modules P) (Line Y)).rightDerivedFunctor.obj
            (P.gysinInput h Y).obj)) ≫
      (sfFiniteExceptionalFixed P.Ring (Compactification.ofIsProper s)).map
        (((comparisonUpperStar (Modules P) (Line Y)).mapDerivedCategoryPlusCompatibility.app
          (P.gysinEtaleInput h Y)).hom)⟦(2 : ℤ)⟧')

/-- Shift by two of the actual finite exceptional counit, with exact closed
image coordinates at its source. This is a construction, before identifying it with
the ordinary etale counit.
Source: finite exceptional adjunction, its displayed counit composite.
(blueprint: def-pur-boundary-shifted-counit). -/
def boundaryShiftedCounit (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    (lowerStar (Modules P) (zeroSection Y)).mapDerivedCategory.obj
        (P.gysinValue h Y) ⟶ (P.gysinInput h Y).obj⟦(2 : ℤ)⟧ := by
  let s := zeroSection Y
  letI := (Compactification.ofIsProper s).hasCompactification
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace a
  letI : QuasiCompact (lineProjection Y) := by
    change QuasiCompact (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)
    infer_instance
  letI : CompactSpace (Line Y) :=
    QuasiCompact.compactSpace_of_compactSpace (lineProjection Y)
  let L := (P.gysinInput h Y).obj
  let R := sfFiniteExceptionalFixed P.Ring (Compactification.ofIsProper s)
  exact ((lowerStar (Modules P) s).mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
      (R.obj L) ≫
    ((lowerStar (Modules P) s).rightDerivedFunctorIsoMapDerivedCategory.inv.app (R.obj L) ≫
      (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (Modules P) s).inv.app
        (R.obj L) ≫ rightDerivedUpperShriekCounit s L (P.gysinInput h Y).property)⟦(2 : ℤ)⟧'

/-- The actual exceptional counit at the shifted input, in exact closed image
coordinates. Its lower bound is inherited from the bounded-below shifted input.
Source: finite exceptional adjunction, inverse Hom equivalence.
(blueprint: def-pur-boundary-shifted-counit). -/
def boundaryExactCounit (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    (lowerStar (Modules P) (zeroSection Y)).mapDerivedCategory.obj
      ((sfFiniteExceptionalFixed P.Ring (Compactification.ofIsProper (zeroSection Y))).obj
        ((P.gysinInput h Y).obj⟦(2 : ℤ)⟧)) ⟶ (P.gysinInput h Y).obj⟦(2 : ℤ)⟧ := by
  let s := zeroSection Y
  letI := (Compactification.ofIsProper s).hasCompactification
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace a
  letI : QuasiCompact (lineProjection Y) := by
    change QuasiCompact (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)
    infer_instance
  letI : CompactSpace (Line Y) :=
    QuasiCompact.compactSpace_of_compactSpace (lineProjection Y)
  let L := (P.gysinInput h Y).obj⟦(2 : ℤ)⟧
  let R := sfFiniteExceptionalFixed P.Ring (Compactification.ofIsProper s)
  have hL : _root_.DerivedCategory.TStructure.t.plus L :=
    _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
      ((_root_.DerivedCategory.Plus.ι.commShiftIso (2 : ℤ)).app (P.gysinInput h Y))
      ((P.gysinInput h Y)⟦(2 : ℤ)⟧).property
  exact (lowerStar (Modules P) s).rightDerivedFunctorIsoMapDerivedCategory.inv.app (R.obj L) ≫
    (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (Modules P) s).inv.app
      (R.obj L) ≫ rightDerivedUpperShriekCounit s L hL

end WeilConjectures.PurityFiniteSetting
