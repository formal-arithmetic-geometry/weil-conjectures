/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.AlgebraicGeometry.CompactProductArrows
public import Sheaf.Paper.SupportedCupFunctoriality

/-! # SupportedTwistPullback

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-supported-twist-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u v c d e w v₁ v₂ v₃
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

open AlgebraicGeometry AlgebraicGeometry.Etale

/-- The exact/left-derived and degree-zero inverse-image comparisons, composed before
specializing the coefficient objects. Source: blueprint Step 1, twist multiplication
(blueprint: def-pur-supported-twist-pullback). -/
def compactProductTwistPullbackCore (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    {X Y : Scheme.{u}} (p : Y ⟶ X) (S : Sheaf X.smallEtaleTopology C)
    (T : Sheaf Y.smallEtaleTopology C) (e : (upperStar C p).obj S ⟶ T) :
    (upperStar C p).leftDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj S) ⟶
      (DerivedCategory.singleFunctor _ 0).obj T :=
  (leftDerivedUpperStarIsoMapDerivedCategory C p).hom.app _ ≫
    ((upperStar C p).mapDerivedCategorySingleFunctor 0).hom.app S ≫
    (DerivedCategory.singleFunctor _ 0).map e

/-- Projection pullback of the actual degree-zero twist, with its canonical
constant-root-line pullback identification.
Source: blueprint Step 1, twist multiplication
(blueprint: def-pur-supported-twist-pullback). -/
def compactProductTwistPullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (p : Y ⟶ X) (f : X ⟶ Spec (.of P.field.k)) (r : ℤ) :=
  compactProductTwistPullbackCore (ModuleCat.{u + 1} P.Coefficient) p
    (P.functorialCupTwist false X r) (P.functorialCupTwist false Y r)
    (P.functorialCupEtaleTwistPullback p f r).hom

end WeilConjectures.PurityFiniteSetting
