/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedHomPullback
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonBoundary
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact

/-! # Geometric pullback of the actual coordinate Kummer boundary

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
thm-pur-affine-line-orientation.proof.md, geometric-fibre sentence; Milne,
Lectures on Etale Cohomology, Theorem 9.4 and Example 9.5
(blueprint: lem-pur-coordinate-boundary-geometric-pullback).

The section-class conversion below derives evaluation of the actual constant unit.
All coefficient maps are the pure-tensor maps of the affine-line datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u u' v v' w w' d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CategoryTheory.Abelian.Ext

end CategoryTheory.Abelian.Ext

namespace WeilConjectures.PurityFiniteSetting

/-- The unit-normalized comparison ladder for the two chosen boundary maps.
Source: naturality of the normalized support snake boundary, Stacks Tag 09XP
(blueprint: def-pur-coordinate-boundary-geometric-pullback-data). -/
def CoordinateBoundaryModel.SiteLadder (P : PurityFiniteSetting.{u})
    {Y : Scheme.{u}} (D : CoordinateBoundaryModel P Y) : Prop :=
  ∀ (q : ℤ) (F : Sheaf (Line Y).smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)),
    (D.boundaryEtale q).app ⟨(DerivedCategory.Plus.singleFunctor _ 0).obj F, trivial⟩ ≫
      (ProEtale.supportComparisonHypercohomology P.Coefficient (zeroSection Y) (q + 1)).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) =
      (ProEtale.finiteComparisonSectionHypercohomology (Line Y) P.Coefficient
        (Scheme.Etale.mk (zeroSection Y).openComplement.ι) q).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      (D.boundaryPro q).app ⟨(ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) (Line Y)).mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F), trivial⟩

end WeilConjectures.PurityFiniteSetting

namespace AlgebraicGeometry.SupportHomPair

variable {A : Type (u + 1)} [CommRing A] {S T : SupportHomPair A}
  {B : S.Site ⥤ T.Site} [hB : B.IsContinuous S.topology T.topology]
  {L : Sheaf S.topology (ModuleCat.{u + 1} A) ⥤
    Sheaf T.topology (ModuleCat.{u + 1} A)}
  {adj : L ⊣ B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) S.topology T.topology}
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

end AlgebraicGeometry.SupportHomPair

namespace WeilConjectures.PurityFiniteSetting

end WeilConjectures.PurityFiniteSetting
