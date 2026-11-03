/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityConventions.PurityConventions
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameKummer
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# The affine line and the punctured line with finite coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
det-prop-a1-kummer.md, clauses (a)--(c) and base change
(blueprint: det-prop-a1-kummer).

We use the recorded all-level root-tensor presentation and its actual Kummer class.
All sheaves are on the small pro-etale site. The exponent is ell^n, so no divisibility
of the coefficient level by the ramification index is imposed. The auxiliary maps are
single-complex, adjunction, and shift composites of the published canonical maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- The existing constant module or all-level finite Tate line, according to the flag.
Source: det-prop-a1-kummer, coefficients in (a)--(c)
(blueprint: det-prop-a1-kummer). -/
abbrev a1KummerCoefficient (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (b : Bool) :=
  if b then P.frameTwist X 1 else P.constant X

/-- Place the specified coefficient sheaf in degree zero.
Source: det-prop-a1-kummer, Rp_* and Rpi_* of the finite coefficients
(blueprint: det-prop-a1-kummer). -/
abbrev a1KummerComplex (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (b : Bool) :=
  (DerivedCategory.singleFunctor _ 0).obj (P.a1KummerCoefficient X b)

/-- Pullback of the existing coefficient sheaves, normalized on constants and root tensors.
Source: det-prop-a1-kummer, base-change paragraph
(blueprint: det-prop-a1-kummer). -/
def a1KummerCoefficientPullback (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Y ⟶ Spec (.of P.field.k)) (b : Bool) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj
      (P.a1KummerCoefficient Y b) ≅ P.a1KummerCoefficient X b :=
  match b with
  | true => P.frameTwistPullback f a 1
  | false => P.frameConstantPullback f

/-- The canonical derived coefficient pullback; it is the single-complex comparison
followed by the recorded root-normalized coefficient isomorphism.
Source: det-prop-a1-kummer, base-change paragraph
(blueprint: det-prop-a1-kummer). -/
def a1KummerPullback (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Y ⟶ Spec (.of P.field.k)) (b : Bool) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj
      (P.a1KummerComplex Y b) ⟶ P.a1KummerComplex X b :=
  (ProEtale.singleFunctorCompLeftDerivedUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) f).hom.app (P.a1KummerCoefficient Y b) ≫
      (DerivedCategory.singleFunctor _ 0).map (P.a1KummerCoefficientPullback f a b).hom

/-- The actual unit with its target identified by the canonical coefficient pullback.
Source: det-prop-a1-kummer, affine-line acyclicity and degree-zero punctured-line unit
(blueprint: det-prop-a1-kummer). -/
def a1KummerUnit (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Y ⟶ Spec (.of P.field.k)) (b : Bool) :
    P.a1KummerComplex Y b ⟶
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor.obj
        (P.a1KummerComplex X b) :=
  (ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} P.Coefficient) f).unit.app (P.a1KummerComplex Y b) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor.map
        (P.a1KummerPullback f a b)

/-- The existing all-level Kummer boundary evaluated on the actual coordinate unit.
Source: det-prop-a1-kummer (b), kappa(t), with det-def-purity-conv
(blueprint: det-prop-a1-kummer). -/
abbrev a1KummerClass (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (a : Y ⟶ Spec (.of P.field.k)) :=
  P.frameKummer (Punctured Y) (puncturedProjection Y ≫ a) (coordinateUnit Y)

/-- The A-linear map sending one to the Leray edge section of the actual coordinate class.
It takes H0 of the adjoint of kappa(t), then uses H0(K[1]) = H1(K).
Source: det-prop-a1-kummer (b), specified Kummer generator
(blueprint: det-prop-a1-kummer). -/
def a1KummerGenerator (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (a : Y ⟶ Spec (.of P.field.k)) :
    P.constant Y ⟶ (DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 1).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection Y)).rightDerivedFunctor.obj
            (P.a1KummerComplex (Punctured Y) true)) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).inv.app
      (P.constant Y) ≫
    (DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).map
      (((ProEtale.derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) (puncturedProjection Y)).homEquiv _ _
          (P.a1KummerPullback (puncturedProjection Y) a false ≫
            (P.a1KummerClass Y a).hom)) ≫
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection Y)).rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
            (P.a1KummerComplex (Punctured Y) true)) ≫
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).shiftIso
        (1 : ℤ) 0 1 (add_zero 1)).hom.app
      ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        (puncturedProjection Y)).rightDerivedFunctor.obj
          (P.a1KummerComplex (Punctured Y) true))

/-- Clauses (a)--(c), including the actual degree-zero unit and degree-one generator.
This predicate also applies to a geometric point with no finite-type condition.
Source: det-prop-a1-kummer (a)--(c)
(blueprint: det-prop-a1-kummer). -/
def A1KummerConclusions (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (a : Y ⟶ Spec (.of P.field.k)) : Prop :=
  IsIso (P.a1KummerUnit (lineProjection Y) a false) ∧
  IsIso ((DerivedCategory.homologyFunctor
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).map
      (P.a1KummerUnit (puncturedProjection Y) a true)) ∧
  IsIso (P.a1KummerGenerator Y a) ∧
  ∀ (m : ℕ), 2 ≤ m → IsZero
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) (m : ℤ)).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection Y)).rightDerivedFunctor.obj
            (P.a1KummerComplex (Punctured Y) true)))

/-- Base change for the actual class and the specified derived exchange maps.
The untwisted affine-line and twisted punctured-line maps are exactly those in (a)--(c).
Source: det-prop-a1-kummer, base-change paragraph
(blueprint: det-prop-a1-kummer). -/
def A1KummerBaseChange (P : PurityFiniteSetting.{u})
    {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (a : Y ⟶ Spec (.of P.field.k)) : Prop :=
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (puncturedMap g)).leftDerivedFunctor.map (P.a1KummerClass Y a).hom ≫
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (puncturedMap g)).leftDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
        (P.a1KummerComplex (Punctured Y) true) ≫
    (P.a1KummerPullback (puncturedMap g) (puncturedProjection Y ≫ a) true)⟦(1 : ℤ)⟧' =
      P.a1KummerPullback (puncturedMap g) (puncturedProjection Y ≫ a) false ≫
        (P.a1KummerClass Y' (g ≫ a)).hom ∧
  IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq).app
      (P.a1KummerComplex (Line Y) false)) ∧
  IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
    (puncturedSquare g)).app (P.a1KummerComplex (Punctured Y) true))

end WeilConjectures.PurityFiniteSetting
