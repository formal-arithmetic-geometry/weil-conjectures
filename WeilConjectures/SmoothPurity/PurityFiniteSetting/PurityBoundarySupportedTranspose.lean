/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityBoundaryComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructureStatement
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityBoundaryClassicalCounitShift
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityBoundaryExceptionalCounitShift

/-! # The ordinary closed counit computes the specified supported transpose -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

/-- The specified supported-Hom map is the direct image of its closed adjunct
followed by the transported ordinary counit. This only compares two descriptions
of a supported transpose, before choosing a boundary or an edge chart.
Source: affine-line orientation proof, final site-comparison sentence;
Milne, closed-support adjunction before Theorem 16.7.

Proof: expand gysinSupportToHom as the finite exceptional adjunct followed by
boundaryAdjunctShift. The inverse Hom equivalence identifies the direct image of
the adjunct followed by the actual exceptional counit with the original source
composite. Classical-input counit normalization identifies boundaryShiftedCounit
with boundaryTransportCounit by cancelling the two invertible comparison maps.
Exceptional-counit shift compatibility then replaces the image of the adjunct
shift followed by that counit with boundaryExactCounit. Naturality of the inverse
closed-image comparisons moves the direct image of the adjunct to the actual
compact-support direct image. Apply the inverse Hom identity, cancel the closed
image comparisons and the single-functor comparison, and recover the displayed
supported morphism. No boundary or edge chart is used in this calculation.
(blueprint: lem-pur-boundary-supported-transpose). -/
theorem boundary_supported_transpose (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (hb : DerivedCategory.TStructure.t.plus (P.boundaryEtaleValue h Y))
    (x : P.gysinSupport h Y) :
    ((show P.BoundarySupportedHom Y from
      supportedCohomologyHom P (zeroSection Y) 2).hom.app (P.gysinInput h Y)) x =
      ((lowerStar (Modules P) (zeroSection Y)).mapDerivedCategorySingleFunctor 0).inv.app
        (P.constant Y) ≫
        (lowerStar (Modules P) (zeroSection Y)).mapDerivedCategory.map
          (P.gysinSupportToHom h Y a x) ≫ P.boundaryTransportCounit h Y hb := by
  let s := zeroSection Y
  let := (Compactification.ofIsProper s).hasCompactification
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace a
  let : QuasiCompact (lineProjection Y) := by
    change QuasiCompact (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)
    infer_instance
  let : CompactSpace (Line Y) :=
    QuasiCompact.compactSpace_of_compactSpace (lineProjection Y)
  let : QuasiCompact (openImmersion Y) := by
    dsimp [openImmersion, Punctured]
    infer_instance
  let : PreservesFiniteColimits (lowerStar (Modules P) s) := by
    let hc : IsCompl (Set.range s.base) (Set.range (openImmersion Y).base) := by
      rw [show Set.range (openImmersion Y).base = (Set.range s.base)ᶜ from
        AffineSpace.range_basicOpen_ι_coord Y]
      exact isCompl_compl
    exact preservesFiniteColimits_lowerStar_of_isCompl (R := P.Coefficient) s
      (openImmersion Y) hc
  let hU : ProEtale.DerivedCategory.plusEtaleOrigin (Modules P) Y
      (P.derivedSheaf h Y false) :=
    (ProEtale.DerivedCategory.plusEtaleOrigin (Modules P) Y).prop_of_iso
      ((comparisonUpperStar (Modules P) Y).mapDerivedCategorySingleFunctor 0 |>.app
        (P.constantEtale Y))
      (ProEtale.DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj
        (show _root_.DerivedCategory.TStructure.t.plus
          ((_root_.DerivedCategory.singleFunctor (EtSheaves P Y) 0).obj
            (P.constantEtale Y)) from ⟨0, inferInstance⟩))
  let hL : _root_.DerivedCategory.TStructure.t.plus ((P.gysinInput h Y).obj⟦(2 : ℤ)⟧) :=
    _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
      ((_root_.DerivedCategory.Plus.ι.commShiftIso (2 : ℤ)).app (P.gysinInput h Y))
      ((P.gysinInput h Y)⟦(2 : ℤ)⟧).property
  let f := (supportedCohomologyHom P s 2).hom.app (P.gysinInput h Y) x
  let e := rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (Modules P) s
  let q := (lowerStar (Modules P) s).rightDerivedFunctorIsoMapDerivedCategory
  let v := e.hom.app (P.derivedSheaf h Y false) ≫
      q.hom.app (P.derivedSheaf h Y false) ≫
      ((lowerStar (Modules P) s).mapDerivedCategorySingleFunctor 0).hom.app
        (P.constant Y) ≫ f
  let m := rightDerivedUpperShriekHomEquiv s hU hL v
  have hm : P.gysinSupportToHom h Y a x = m ≫ P.boundaryAdjunctShift h Y := by
    rfl
  have hv :
      (rightDerivedLowerShriek (Modules P) s).map m ≫
        rightDerivedUpperShriekCounit s ((P.gysinInput h Y).obj⟦(2 : ℤ)⟧) hL = v := by
    exact (rightDerivedUpperShriekHomEquiv s hU hL).symm_apply_apply v
  have hc : P.boundaryShiftedCounit h Y a = P.boundaryTransportCounit h Y hb := by
    let := boundaryExceptionalComparison_isIso P h Y
    let := boundaryImageComparison_isIso P Y ⟨P.boundaryEtaleValue h Y, hb⟩
    apply (cancel_epi
      (P.boundaryImageComparison Y ⟨P.boundaryEtaleValue h Y, hb⟩ ≫
        (lowerStar (Modules P) s).mapDerivedCategory.map
          (P.boundaryExceptionalComparison h Y))).1
    simpa only [Category.assoc] using
      (boundary_classical_counit_shift P h Y a hb).trans
        (boundaryTransportCounit_eq P h Y hb).symm
  rw [hm, Functor.map_comp, Category.assoc, ← hc,
    boundary_exceptional_counit_shift P h Y a]
  have ht : (lowerStar (Modules P) s).mapDerivedCategory.map m ≫
      P.boundaryExactCounit h Y a =
      ((lowerStar (Modules P) s).mapDerivedCategorySingleFunctor 0).hom.app
        (P.constant Y) ≫ f := by
    change (lowerStar (Modules P) s).mapDerivedCategory.map m ≫ q.inv.app _ ≫
      e.inv.app _ ≫ rightDerivedUpperShriekCounit s _ hL = _
    rw [reassoc_of% q.inv.naturality m, reassoc_of% e.inv.naturality m, hv]
    dsimp only [v]
    simp only [Iso.inv_hom_id_app_assoc]
  change f = _
  rw [ht, Iso.inv_hom_id_app_assoc]

end WeilConjectures.PurityFiniteSetting
