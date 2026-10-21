/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.Paper.QuotientExchangeScalarComparisons
public import Sheaf.Paper.RingedExchangeTensorCoherence
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.RingedComparisonTensorAdjunction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedStrictTowerProjectionMorphism
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison

/-! # The strict perfect-coefficient exchange and its coaugmentation

Source: Stacks Project, sites-cohomology.tex, Tags 0E48 and 0944;
strict augmented perfect-diagram refinement, agent supplied
(blueprint: lem-sbc-strict-quotient-exchange-unit-equation).

All towers are objects of the derived category of strict module diagrams.
The presentation data below fix maps on complexes before localization.

## Main definitions and statements

`strictQuotientExchangeUnitEquation` states the exchange and coaugmentation equations.
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

/-- Pointwise local perfectness of the strict coefficient sequence.
Source: Stacks 08G5, 0944
(blueprint: lem-sbc-strict-quotient-exchange-unit-equation). -/
def HasPerfectLevels (A : RingedTensorCorner.{u, w})
    (Q : ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ) : Prop :=
  letI : HasSheafify A.topology AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  letI : ∀ U : A.site, HasSheafify (A.topology.over U) AddCommGrpCat.{u} :=
    fun _U ↦ GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  letI : ∀ U : A.site, (A.topology.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    fun _U ↦ inferInstance
  letI : A.topology.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  ∀ n : ℕᵒᵖ, IsPerfectOnRingedSiteOfUniverses.{u, u, 0, w} A.ring
    (DerivedCategory.Q.obj (Q.obj n))

/-- Invertibility of the two canonical projection maps.
Source: Stacks 0E48, 0944; strict augmented refinement
(blueprint: lem-sbc-strict-quotient-exchange-unit-equation). -/
def ProjectionIsomorphisms {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh) : Prop :=
  ∀ K : T.mateDerived,
    IsIso (firstProjection q ag K) ∧ IsIso (secondProjection q ah K)

/-- Equality with the actual square mate as a whole strict-tower morphism.
Source: Stacks 0E48, 0944; strict augmented refinement
(blueprint: lem-sbc-strict-quotient-exchange-unit-equation). -/
def IsTowerMate {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (K : T.mateDerived) [IsIso (firstProjection q ag K)] : Prop :=
  conjugate q ag ah K = (towerMate f g h e s ag ah).app (input q K)

/-- The ambient coefficient-tensor square mate under normalized evaluation.
Source: Stacks 0E48, 0944; strict augmented refinement
(blueprint: lem-sbc-strict-quotient-exchange-unit-equation). -/
def IsEvaluatedMate {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (K : T.mateDerived) [IsIso (firstProjection q ag K)] : Prop :=
  ∀ n : ℕᵒᵖ,
    (ev X lX n).map (conjugate q ag ah K) ≫ (evaluatedTarget q dh K n).hom =
      (evaluatedSource q dg K n).hom ≫
        s.exchange.app ((ev T lT n).obj (input q K))

/-- The strict augmentation and inverse-limit coaugmentation equation.
Source: Stacks 0E48, 0944; strict augmented refinement
(blueprint: lem-sbc-strict-quotient-exchange-unit-equation). -/
def HasCoaugmentationEquation {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (jX : ConstantLimit X lX) (jY : ConstantLimit Y lY)
    (K : T.mateDerived) [IsIso (firstProjection q ag K)] : Prop :=
  (kappa q.atX.r lX jX).app (f.left.obj (g.right.obj K)) ≫ gamma q ag ah K =
    s.exchange.app K ≫ h.right.map ((kappa q.atY.r lY jY).app (e.left.obj K))

/-- Naturality of the displayed derived-limit exchange in the input complex.
Source: Stacks 0E48, 0944; strict augmented refinement
(blueprint: lem-sbc-strict-quotient-exchange-unit-equation). -/
def IsNaturalGamma {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh) : Prop :=
  ∀ (K K' : T.mateDerived) [IsIso (firstProjection q ag K)]
    [IsIso (firstProjection q ag K')] (a : K ⟶ K'),
    (completion q.atX.r lX).map (f.left.map (g.right.map a)) ≫ gamma q ag ah K' =
      gamma q ag ah K ≫ h.right.map ((completion q.atY.r lY).map (e.left.map a))

/-- All strict exchange, evaluation, quotient and coaugmentation conclusions.
This is the conjunction of the displayed named equations, with no further data.
Source: Stacks 0E48, 0944; strict augmented refinement
(blueprint: lem-sbc-strict-quotient-exchange-unit-equation). -/
def FullEquation {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (jX : ConstantLimit X lX) (jY : ConstantLimit Y lY) : Prop :=
    ProjectionIsomorphisms q ag ah ∧
    (∀ (K : T.mateDerived) [IsIso (firstProjection q ag K)],
      IsTowerMate q ag ah K ∧ IsEvaluatedMate q ag ah K ∧ QuotientEquation q ag ah K ∧
        HasCoaugmentationEquation q ag ah jX jY K) ∧
    IsNaturalGamma q ag ah

/-- Strict perfect-coefficient exchange, its evaluated and quotient-ring mates, and
its coaugmentation equation after total derived inverse limit.
Source: Stacks Project, sites-cohomology.tex, Tags 0E48 and 0944; strict augmented
perfect-diagram/coaugmentation refinement, agent supplied
(blueprint: lem-sbc-strict-quotient-exchange-unit-equation).Proof:
1. Use the small diagram-site realization and normalized evaluation comparisons
(lem-weil-pbc-diagram-site-realization, lem-weil-pbc-tower-derived-evaluation-normalization).
The constant-direct-image comparison is fixed by the ordinary counit, so the
constant-tower mate is Delta of the ambient mate
(lem-weil-pbc-constant-tower-pushforward-normalization).
2. Evaluate H and H'. Each evaluation is the perfect-coefficient projection map
of lem-sbc-ringed-site-perfect-projection-formula (Stacks 0944). Pullback preserves
local perfectness by lem-weil-pbc-strict-perfect-ringed-pullback-model and a covering
argument. Cones are acyclic levelwise by lem-weil-tower-category-levelwise-abelian;
therefore H and H' are isomorphisms of derived strict towers.
3. Apply lem-weil-pbc-ringed-exchange-tensor-coherence on the diagram topoi to
Delta K and the coefficient diagram. It gives beta H = H' R(b). Cancel H.
This proves equality of whole-tower morphisms without using evaluations to detect equality.
4. Evaluate the actual mate, using the counit-preserving comparisons. Its transpose
is the ambient square comparison followed by the ambient counit. For quotient
coefficients, apply lem-pur-diagram-ring-restriction-pushforward and
lem-sfb-ringed-comparison-tensor-adjunction. The composite-counit and ring-square
normalizations identify the restricted quotient mate with this evaluated mate.
5. Naturality of the projection map in coefficients, and its identity value at the
unit (lem-weil-pbc-ringed-projection-mate-exact), give H' i_X = R_h(i_Y) chi_h
as an equation before taking limits, for the actual strict augmentation.
6. Naturality of the canonical direct-image/limit comparison, normalized on constant
towers, gives c inverse Rlim(H') kappa_X = R_h(kappa_Y)
(lem-weil-ringed-tower-pushforward-limit-comparison,
lem-weil-pbc-constant-tower-pushforward-normalization,
lem-weil-pbc-ringed-strict-tower-homotopy-limit).
7. Naturality of the augmentation gives C_X(b) kappa_M = kappa_N b. Substitute
v H = H' R_X(b) into c inverse Rlim(v) Rlim(H) kappa_M. The result is
R_h(kappa_Y) b. Naturality in K follows from naturality of every construction.
No completeness, reflector, cartesianness, or geometric-finiteness hypothesis enters. -/
theorem strictQuotientExchangeUnitEquation
    (s : RingedTensorSquare S T X Y g f e h)
    (q : Coefficients f g h e s)
    (hperfect : HasPerfectLevels S q.atS.Q)
    (hf : IsIso f.ringMap) (hg : IsIso g.ringMap)
    (hh : IsIso h.ringMap) (he : IsIso e.ringMap)
    (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (jX : ConstantLimit X lX) (jY : ConstantLimit Y lY) :
    FullEquation q ag ah jX jY := by
  sorry

end SheafOfModules.StrictQuotientExchange
