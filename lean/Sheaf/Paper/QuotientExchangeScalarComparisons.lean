/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.Paper.StrictCoefficientExchangeArrows
public import Sheaf.Paper.QuotientCoefficientPresentation
public import Sheaf.Paper.RingedExchangeTensorCoherence
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.RingedComparisonTensorAdjunction

/-! # The strict perfect-coefficient exchange and its coaugmentation

Source: Stacks Project, sites-cohomology.tex, Tags 0E48 and 0944;
strict augmented perfect-diagram refinement, agent supplied
(blueprint: def-sbc-quotient-exchange-scalar-comparisons).

All towers are objects of the derived category of strict module diagrams.
The presentation data below fix maps on complexes before localization.

## Main definitions and statements

`QuotientAt`, `QuotientComparisons`, and `QuotientEquation` specify quotient
coefficient models and their scalar-restriction comparison equation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
-- Keep normalized representative proofs in the public definitions.
set_option backward.proofsInPublic true
set_option synthInstance.maxSize 2048
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w uData vData wData xData yData zData

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.StrictQuotientExchange

/-- Compatibility of scalar restriction with the adjunction counit.
Source: Stacks 03EL, 0E48
(blueprint: def-sbc-quotient-exchange-scalar-comparisons). -/
def quotientCounitNormalized {A B : RingedTensorCorner.{u, w}}
    {QA : CochainComplex A.mateModules ℤ} {QB : CochainComplex B.mateModules ℤ}
    (g : RingedTensorEdge A B) (aA : QuotientAt A QA) (aB : QuotientAt B QB)
    (gq : RingedTensorEdge (quotientCorner aA) (quotientCorner aB)) :
    (gq.left ⋙ forgetQuotient aB ≅ forgetQuotient aA ⋙ g.left) →
      (gq.right ⋙ forgetQuotient aA ≅ forgetQuotient aB ⋙ g.right) → Prop :=
  (fun lg rg ↦ ∀ J : (quotientCorner aB).mateDerived,
    (forgetQuotient aB).map (gq.derivedAdjunction.counit.app J) =
      lg.hom.app (gq.right.obj J) ≫ g.left.map (rg.hom.app J) ≫
        g.derivedAdjunction.counit.app ((forgetQuotient aB).obj J))

variable {S T X Y : RingedTensorCorner.{u, w}}
  (f : RingedTensorEdge S X) (g : RingedTensorEdge S T)
  (h : RingedTensorEdge X Y) (e : RingedTensorEdge T Y)
  [PreservesFiniteLimits f.pullback] [PreservesFiniteColimits f.pullback]
  [PreservesFiniteLimits g.pullback] [PreservesFiniteColimits g.pullback]
  [PreservesFiniteLimits h.pullback] [PreservesFiniteColimits h.pullback]
  [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
  [HasDerivedCategory.{w} S.projectionTowers]
  [HasDerivedCategory.{w} T.projectionTowers]
  [HasDerivedCategory.{w} X.projectionTowers]
  [HasDerivedCategory.{w} Y.projectionTowers]

variable [g.pushforward.Additive] [h.pushforward.Additive]
  [HasCountableProducts S.mateDerived] [HasCountableProducts T.mateDerived]
  [HasCountableProducts X.mateDerived] [HasCountableProducts Y.mateDerived]
  {lS : StrictProjectionLimit S} {lT : StrictProjectionLimit T}
  {lX : StrictProjectionLimit X} {lY : StrictProjectionLimit Y}
  {dg : StrictProjectionDirectImage g lT lS} {dh : StrictProjectionDirectImage h lY lX}

variable {f g h e}

/-- Scalar-restriction comparisons with their counit and square normalizations.
The generic record retains exactly the six comparisons and three equations.
Source: Stacks 03EL, 0E48
(blueprint: def-sbc-quotient-exchange-scalar-comparisons). -/
structure QuotientComparisonsData
    (A : Type uData) (B : Type vData) (C : Type wData)
    (D : Type xData) (E : Type yData) (F : Type zData)
    (G : B → E → Prop) (H : C → F → Prop) (S : A → B → C → D → Prop) where
  lf : A
  lg : B
  lh : C
  le : D
  rg : E
  rh : F
  counit_g : G lg rg
  counit_h : H lh rh
  square : S lf lg lh le

/-- Compatibility of scalar restriction with the inverse-image square.
Source: Stacks 03EL, 0E48
(blueprint: def-sbc-quotient-exchange-scalar-comparisons). -/
def quotientSquareNormalized
    {QS : CochainComplex S.mateModules ℤ} {QT : CochainComplex T.mateModules ℤ}
    {QX : CochainComplex X.mateModules ℤ} {QY : CochainComplex Y.mateModules ℤ}
    (aS : QuotientAt S QS) (aT : QuotientAt T QT)
    (aX : QuotientAt X QX) (aY : QuotientAt Y QY)
    (fq : RingedTensorEdge (quotientCorner aS) (quotientCorner aX))
    (gq : RingedTensorEdge (quotientCorner aS) (quotientCorner aT))
    (hq : RingedTensorEdge (quotientCorner aX) (quotientCorner aY))
    (eq : RingedTensorEdge (quotientCorner aT) (quotientCorner aY))
    (s : RingedTensorSquare S T X Y g f e h)
    (sq : RingedTensorSquare _ _ _ _ gq fq eq hq) : (fq.left ⋙ forgetQuotient aX ≅ forgetQuotient
      aS ⋙ f.left) → (gq.left ⋙ forgetQuotient aT ≅ forgetQuotient aS ⋙ g.left) → (hq.left ⋙
      forgetQuotient aY ≅ forgetQuotient aX ⋙ h.left) → (eq.left ⋙ forgetQuotient aY ≅
      forgetQuotient aT ⋙ e.left) → Prop :=
  (fun lf lg lh le ↦ ∀ J : (quotientCorner aS).mateDerived,
    (forgetQuotient aY).map (sq.derivedComparison.hom.app J) ≫
        le.hom.app (gq.left.obj J) ≫ e.left.map (lg.hom.app J) =
      lh.hom.app (fq.left.obj J) ≫ h.left.map (lf.hom.app J) ≫
        s.derivedComparison.hom.app ((forgetQuotient aS).obj J))

/-- Quotient scalar comparisons with their named normalization predicates.
Source: Stacks 03EL, 0E48
(blueprint: def-sbc-quotient-exchange-scalar-comparisons). -/
abbrev QuotientComparisons {s : RingedTensorSquare S T X Y g f e h}
    {QS : CochainComplex S.mateModules ℤ} {QT : CochainComplex T.mateModules ℤ}
    {QX : CochainComplex X.mateModules ℤ} {QY : CochainComplex Y.mateModules ℤ}
    (aS : QuotientAt S QS) (aT : QuotientAt T QT)
    (aX : QuotientAt X QX) (aY : QuotientAt Y QY)
    (fq : RingedTensorEdge (quotientCorner aS) (quotientCorner aX))
    (gq : RingedTensorEdge (quotientCorner aS) (quotientCorner aT))
    (hq : RingedTensorEdge (quotientCorner aX) (quotientCorner aY))
    (eq : RingedTensorEdge (quotientCorner aT) (quotientCorner aY))
    (sq : RingedTensorSquare _ _ _ _ gq fq eq hq) :=
  QuotientComparisonsData
    (fq.left ⋙ forgetQuotient aX ≅ forgetQuotient aS ⋙ f.left)
    (gq.left ⋙ forgetQuotient aT ≅ forgetQuotient aS ⋙ g.left)
    (hq.left ⋙ forgetQuotient aY ≅ forgetQuotient aX ⋙ h.left)
    (eq.left ⋙ forgetQuotient aY ≅ forgetQuotient aT ⋙ e.left)
    (gq.right ⋙ forgetQuotient aS ≅ forgetQuotient aT ⋙ g.right)
    (hq.right ⋙ forgetQuotient aX ≅ forgetQuotient aY ⋙ h.right)
    (quotientCounitNormalized g aS aT gq)
    (quotientCounitNormalized h aX aY hq)
    (quotientSquareNormalized aS aT aX aY fq gq hq eq s sq)

/-- The quotient-ring clause, expressed on every quotient-module representative of
an evaluated input and under the indicated scalar-restriction comparisons. The input
identification is used on both ends; no fullness or faithfulness of restriction is used.
Source: Stacks 03EL, 0E48
(blueprint: def-sbc-quotient-exchange-scalar-comparisons). -/
def QuotientEquationAt (s : RingedTensorSquare S T X Y g f e h)
    (QS : CochainComplex S.mateModules ℤ) (QT : CochainComplex T.mateModules ℤ)
    (QX : CochainComplex X.mateModules ℤ) (QY : CochainComplex Y.mateModules ℤ)
    (U : T.mateDerived) (B D : X.mateDerived) (v : B ⟶ D)
    (source : B ≅ f.left.obj (g.right.obj U))
    (target : D ≅ h.right.obj (e.left.obj U)) : Prop :=
  ∀ (aS : QuotientAt S QS) (aT : QuotientAt T QT)
    (aX : QuotientAt X QX) (aY : QuotientAt Y QY)
    (fq : RingedTensorEdge (quotientCorner aS) (quotientCorner aX))
    (gq : RingedTensorEdge (quotientCorner aS) (quotientCorner aT))
    (hq : RingedTensorEdge (quotientCorner aX) (quotientCorner aY))
    (eq : RingedTensorEdge (quotientCorner aT) (quotientCorner aY))
    (sq : RingedTensorSquare _ _ _ _ gq fq eq hq)
    (c : QuotientComparisons (s := s) aS aT aX aY fq gq hq eq sq)
    (J : (quotientCorner aT).mateDerived)
    (i : (forgetQuotient aT).obj J ≅ U),
      (forgetQuotient aX).map (sq.exchange.app J) ≫
          c.rh.hom.app (eq.left.obj J) ≫ h.right.map (c.le.hom.app J) ≫
          h.right.map (e.left.map i.hom) ≫ target.inv =
        c.lf.hom.app (gq.right.obj J) ≫ f.left.map (c.rg.hom.app J) ≫
          f.left.map (g.right.map i.hom) ≫ source.inv ≫
          v

/-- The quotient coefficient equation at every evaluation of the canonical tower map.
Source: Stacks 03EL, 0E48
(blueprint: def-sbc-quotient-exchange-scalar-comparisons). -/
def QuotientEquation {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (K : T.mateDerived) [IsIso (firstProjection q ag K)] : Prop :=
  ∀ n : ℕᵒᵖ, QuotientEquationAt s
    (q.atS.Q.obj n) (q.atT.Q.obj n) (q.atX.Q.obj n) (q.atY.Q.obj n)
    ((ev T lT n).obj (input q K))
    ((ev X lX n).obj (upper q dg K)) ((ev X lX n).obj (lower q dh K))
    ((ev X lX n).map (conjugate q ag ah K))
    (evaluatedSource q dg K n) (evaluatedTarget q dh K n)

end SheafOfModules.StrictQuotientExchange
