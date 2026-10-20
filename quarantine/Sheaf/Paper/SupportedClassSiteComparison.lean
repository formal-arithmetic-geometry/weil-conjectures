/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.Paper.SupportedClassGeometry

/-! # SupportedClassSiteComparison

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-supported-class-site-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v c d e w v₁ v₂ v₃
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

open AlgebraicGeometry AlgebraicGeometry.Etale

/-- Map into a shifted degree-zero object by exact comparison before specializing
its source category or coefficient objects.
Source: blueprint Step 1, finite site comparison
(blueprint: def-pur-supported-class-site-comparison). -/
def compactProductCompareTargetCore {B D : Type c} [Category.{v} B] [Category.{v} D]
    [Abelian B] [Abelian D] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} D]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℤ) {K : DerivedCategory B} (T : B)
    (α : K ⟶ ((DerivedCategory.singleFunctor B 0).obj T)⟦n⟧) :
    F.mapDerivedCategory.obj K ⟶ ((DerivedCategory.singleFunctor D 0).obj (F.obj T))⟦n⟧ :=
  F.mapDerivedCategory.map α ≫
    (F.mapDerivedCategory.commShiftIso n).hom.app ((DerivedCategory.singleFunctor B 0).obj T) ≫
    ((F.mapDerivedCategorySingleFunctor 0).hom.app T)⟦n⟧'

/-- Transport a supported exterior representative to the pro-etale site using
exact comparison inverse image, its shift comparison and its degree-zero comparison.
Source: blueprint Step 1, finite site comparison
(blueprint: def-pur-supported-class-site-comparison). -/
def compactProductCompareClass (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (n r : ℤ)
    {F : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))}
    (α : F ⟶ ((P.functorialCupSingle false X).obj
      (P.functorialCupTwist false X r))⟦n⟧) :
    (P.functorialCupComparisonFunctor X).mapDerivedCategory.obj F ⟶
      ((P.functorialCupSingle true X).obj (P.functorialCupTwist true X r))⟦n⟧ :=
  compactProductCompareTargetCore (P.functorialCupComparisonFunctor X) n
      (P.functorialCupTwist false X r) α ≫
    ((P.functorialCupSingle true X).map
      (eqToHom (P.functorialCupComparisonTwist_eq X r)))⟦n⟧'

/-- Compare a map into a degree-zero source and apply a given coefficient map.
Source: blueprint Step 1, finite site comparison
(blueprint: def-pur-supported-class-site-comparison). -/
def compactProductCompareSourceCore {B D : Type c} [Category.{v} B] [Category.{v} D]
    [Abelian B] [Abelian D] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} D]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K : DerivedCategory B} (S : B) {T : D}
    (α : K ⟶ (DerivedCategory.singleFunctor B 0).obj S) (e : F.obj S ⟶ T) :
    F.mapDerivedCategory.obj K ⟶ (DerivedCategory.singleFunctor D 0).obj T :=
  F.mapDerivedCategory.map α ≫ (F.mapDerivedCategorySingleFunctor 0).hom.app S ≫
    (DerivedCategory.singleFunctor D 0).map e

/-- The comparison of the exterior class's tensor coefficient source with the
pro-etale supported unit, normalized by the recorded closed-constant comparison.
Source: blueprint Step 1, finite site comparison
(blueprint: def-pur-supported-class-site-comparison). -/
def compactProductCompareSource (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  compactProductCompareSourceCore (P.functorialCupComparisonFunctor X)
    (P.functorialCupSource false i) (P.compactProductClassSource i)
    (P.functorialCupComparisonSource_existsUnique i).choose.hom

end WeilConjectures.PurityFiniteSetting
