/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.CategoryTheory.SmoothPurity.BifunctorProjectionCoherence
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.DerivedTensorBraidingShift

/-!
# Constant tensor for a proper exceptional adjoint over any field

Source: Zheng, Construction 2.26, equation (2.26.1), printed p. 15, and
Proposition 2.29(2), printed p. 16, with base `Spec k`
(blueprint: lem-sfb-arbitrary-field-exceptional-constant-tensor).

The projection isomorphism uses the ordered proper projection map and the canonical
pullback identification of termwise constant complexes. Its inverse and the specified
adjunction counit define the exceptional tensor map by transposition.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]

/-- The ordered proper projection isomorphism for a constant coefficient complex.
Its hom is signed symmetry, the canonical proper projection map, direct image of
signed symmetry, and the canonical pullback-of-constants identification.
Source: Zheng, Theorem 2.18(2) and Construction 2.26, printed pp. 12 and 15;
`lem-amb-proper-coproducts-projection`
(blueprint: lem-sfb-arbitrary-field-exceptional-constant-tensor). -/
noncomputable def properConstantProjectionIso
    (V : DerivedCategory (ModuleCat.{u + 1} A)) (K : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj ((constantFunctor A Y).obj V)).obj
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K) ≅
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((constantFunctor A X).obj V)).obj K) :=
  letI := isIso_rightDerivedLowerStarProjectionMap_of_finite A f
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).app
      ((constantFunctor A Y).obj V)).app _ ≪≫
    ((asIso (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f)).app K).app
      ((constantFunctor A Y).obj V) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.mapIso
      (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).app K).app _ ≪≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso
          ((constantFunctorCompLeftDerivedUpperStarIso A f).app V)).app K)

end AlgebraicGeometry.Etale
