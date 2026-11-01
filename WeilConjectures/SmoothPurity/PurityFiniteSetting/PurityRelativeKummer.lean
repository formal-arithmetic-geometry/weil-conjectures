/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Relative affine-line acyclicity and the actual Kummer generator

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer/prop-pur-gm-relative-kummer.md
(blueprint: prop-pur-gm-relative-kummer).

All objects below are actual finite-coefficient module sheaves on the small pro-etale
site. The maps are the units and canonical exchange mates of the published functors.
The generator is homology of the adjoint of the coordinate's actual Kummer boundary.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- Canonical pullback on constants, with comparison inverse images included.
Source: blueprint sk-def-purity-conv (blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def constantPullback (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj (P.constant Y) ⟶
      P.constant X :=
  (ProEtale.comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) f).hom.app (P.constantEtale Y) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) f).hom.app
          (ModuleCat.of P.Coefficient P.Coefficient))

/-- Canonical pullback on the finite twist, with comparison inverse images included.
Source: blueprint sk-def-purity-conv (blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def twistPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj (P.twist h Y) ⟶
      P.twist h X :=
  (ProEtale.comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) f).hom.app (P.twistEtale h Y) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
        (P.twistEtalePullback h f)

/-- Pullback of a coefficient object in the derived category. This is the standard
single-complex comparison followed by the canonical map on the actual sheaves.
Source: blueprint sk-def-purity-conv (blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def derivedCoefficientPullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) (twisted : Bool) :
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor).obj
      (P.derivedSheaf h Y twisted) ⟶ P.derivedSheaf h X twisted :=
  (ProEtale.singleFunctorCompLeftDerivedUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) f).hom.app (P.coefficientSheaf h Y twisted) ≫
      (DerivedCategory.singleFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) 0).map
          (match twisted with
            | true => P.twistPullback h f
            | false => P.constantPullback f)

/-- The canonical unit with coefficients identified by their canonical pullback map.
Source: blueprint sk-prop-a1-kummer, clauses (1) and (2)
(blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def relativeUnit (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) (twisted : Bool) :
    P.derivedSheaf h Y twisted ⟶
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor.obj
        (P.derivedSheaf h X twisted) :=
  (ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} P.Coefficient) f).unit.app (P.derivedSheaf h Y twisted) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) f).rightDerivedFunctor.map
        (P.derivedCoefficientPullback h f twisted)

/-- The edge-section map, obtained by transposing the actual coordinate class and
taking H0, followed by the standard H0(K[1])=H1(K) comparison. It is the A-linear map
whose value on 1 is the Leray edge image of kappa(t).
Source: blueprint sk-prop-a1-kummer, clause (2)
(blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def kummerGenerator (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) :
    P.constant Y ⟶ (DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 1).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection Y)).rightDerivedFunctor.obj
            (P.derivedSheaf h (Punctured Y) true)) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).inv.app
      (P.constant Y) ≫
    (DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).map
      (((ProEtale.derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} P.Coefficient) (puncturedProjection Y)).homEquiv _ _
          (P.derivedCoefficientPullback h (puncturedProjection Y) false ≫
            (P.coordinateKummer h Y a).hom)) ≫
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection Y)).rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
            (P.derivedSheaf h (Punctured Y) true)) ≫
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).shiftIso
        (1 : ℤ) 0 1 (add_zero 1)).hom.app
      ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        (puncturedProjection Y)).rightDerivedFunctor.obj (P.derivedSheaf h (Punctured Y) true))

/-- The assertions in clauses (1)-(3), with the actual specified maps. No finite-type
condition is built into this predicate, so it also applies to geometric fibres.
Source: blueprint sk-prop-a1-kummer, clauses (1)-(3)
(blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def RelativeKummerConclusions (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) : Prop :=
  IsIso (P.relativeUnit h (lineProjection Y) false) ∧
  IsIso (P.relativeUnit h (lineProjection Y) true) ∧
  (∀ (m : ℕ), 0 < m → IsZero
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) (m : ℤ)).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (lineProjection Y)).rightDerivedFunctor.obj (P.derivedSheaf h (Line Y) true)))) ∧
  IsIso ((DerivedCategory.homologyFunctor
    (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) 0).map
      (P.relativeUnit h (puncturedProjection Y) true)) ∧
  IsIso (P.kummerGenerator h Y a) ∧
  ∀ (m : ℕ), 2 ≤ m → IsZero
    ((DerivedCategory.homologyFunctor
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)) (m : ℤ)).obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
          (puncturedProjection Y)).rightDerivedFunctor.obj
            (P.derivedSheaf h (Punctured Y) true)))

/-- Clause (4): naturality of the actual coordinate class and invertibility of the
canonical exchange mates. Their targets use the canonical coefficient pullback
identifications; invertibility is equivalently tested before those identifications.
Source: blueprint sk-prop-a1-kummer, clause (4)
(blueprint: prop-pur-gm-relative-kummer). -/
noncomputable def KummerBaseChangeConclusions (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {Y' Y : Scheme.{u}} (g : Y' ⟶ Y)
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) : Prop :=
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (puncturedMap g)).leftDerivedFunctor.map (P.coordinateKummer h Y a).hom ≫
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (puncturedMap g)).leftDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
        (P.derivedSheaf h (Punctured Y) true) ≫
    (P.derivedCoefficientPullback h (puncturedMap g) true)⟦(1 : ℤ)⟧' =
      P.derivedCoefficientPullback h (puncturedMap g) false ≫
        (P.coordinateKummer h Y' (g ≫ a)).hom ∧
  IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).toCommSq).app
      (P.derivedSheaf h (Line Y) true)) ∧
  IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
    (puncturedSquare g)).app (P.derivedSheaf h (Punctured Y) true))

end WeilConjectures.PurityFiniteSetting
