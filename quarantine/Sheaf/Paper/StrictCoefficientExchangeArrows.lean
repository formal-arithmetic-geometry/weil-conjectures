/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.Paper.StrictAugmentedCoefficientPresentation
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
(blueprint: def-sbc-strict-coefficient-exchange-arrows).

All towers are objects of the derived category of strict module diagrams.
The presentation data below fix maps on complexes before localization.

## Main definitions and statements

`firstProjection`, `secondProjection`, `conjugate`, and `gamma` are the canonical
exchange arrows. `evaluatedSource` and `evaluatedTarget` identify their evaluations.
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

/-- The input of the strict diagram-site square mate.
Source: Stacks 0E48 (blueprint: def-sbc-strict-coefficient-exchange-arrows). -/
abbrev input {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (K : T.mateDerived) := q.atT.r.functor.obj K

/-- The upper tower in the exchange rectangle.
Source: Stacks 0E48 (blueprint: def-sbc-strict-coefficient-exchange-arrows). -/
abbrev upper {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (dg : StrictProjectionDirectImage g lT lS)
    (K : T.mateDerived) := (towerLeft f).obj (dg.Rt.obj (input q K))

/-- The lower tower in the exchange rectangle.
Source: Stacks 0E48 (blueprint: def-sbc-strict-coefficient-exchange-arrows). -/
abbrev lower {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (dh : StrictProjectionDirectImage h lY lX)
    (K : T.mateDerived) := dh.Rt.obj ((towerLeft e).obj (input q K))

/-- The projection-formula arrow H, with pullback/tensor reassociation included.
Source: Stacks 0944 (blueprint: def-sbc-strict-coefficient-exchange-arrows). -/
def firstProjection {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (K : T.mateDerived) :
    q.atX.r.functor.obj (f.left.obj (g.right.obj K)) ⟶ upper q dg K :=
  q.pf.pull.inv.app (g.right.obj K) ≫
    (towerLeft f).map (projection g ag q.pg K)

/-- The projection-formula arrow H', with the coefficient e-pullback comparison included.
Source: Stacks 0944 (blueprint: def-sbc-strict-coefficient-exchange-arrows). -/
def secondProjection {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ah : TowerAdjunction h dh) (K : T.mateDerived) :
    q.atX.r.functor.obj (h.right.obj (e.left.obj K)) ⟶ lower q dh K :=
  projection h ah q.ph (e.left.obj K) ≫ dh.Rt.map (q.pe.pull.inv.app K)

/-- The projection-formula conjugate v. Invertibility of H is a conclusion of the theorem.
Source: Stacks 0E48, 0944
(blueprint: def-sbc-strict-coefficient-exchange-arrows). -/
def conjugate {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (K : T.mateDerived) [IsIso (firstProjection q ag K)] : upper q dg K ⟶ lower q dh K :=
  inv (firstProjection q ag K) ≫ q.atX.r.functor.map (s.exchange.app K) ≫
    secondProjection q ah K

/-- The canonical direct-image/derived-limit comparison c, with the e-reassociation.
Source: Stacks 0A07 (blueprint: def-sbc-strict-coefficient-exchange-arrows). -/
def limitComparison {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (dh : StrictProjectionDirectImage h lY lX)
    (K : T.mateDerived) :
    h.right.obj ((completion q.atY.r lY).obj (e.left.obj K)) ≅ lX.L.obj (lower q dh K) :=
  dh.a.app (q.atY.r.functor.obj (e.left.obj K)) ≪≫
    lX.L.mapIso (dh.Rt.mapIso (q.pe.pull.symm.app K))

/-- The natural limit exchange gamma, as the displayed composite c inverse, Rlim(v), Rlim(H).
Source: Stacks 0E48, 0A07
(blueprint: def-sbc-strict-coefficient-exchange-arrows). -/
def gamma {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh)
    (K : T.mateDerived) [IsIso (firstProjection q ag K)] :
    (completion q.atX.r lX).obj (f.left.obj (g.right.obj K)) ⟶
      h.right.obj ((completion q.atY.r lY).obj (e.left.obj K)) :=
  lX.L.map (firstProjection q ag K) ≫ lX.L.map (conjugate q ag ah K) ≫
    (limitComparison q dh K).inv

/-- The evaluation supplied with the actual derived-limit model.
Source: Stacks 0A07 (blueprint: def-sbc-strict-coefficient-exchange-arrows). -/
abbrev ev (A : RingedTensorCorner.{u, w})
    [HasDerivedCategory.{w} A.projectionTowers] [HasCountableProducts A.mateDerived]
    (l : StrictProjectionLimit A) (n : ℕᵒᵖ) :=
  l.ev ⋙ (CategoryTheory.evaluation ℕᵒᵖ A.mateDerived).obj n

/-- The prescribed evaluation model agrees with exact evaluation, by localization of
its representative identification. This is a whole-diagram comparison, not a choice
of isomorphisms between components.
Source: Stacks 0A07 (blueprint: def-sbc-strict-coefficient-exchange-arrows). -/
def evComparison (A : RingedTensorCorner.{u, w})
    [HasDerivedCategory.{w} A.projectionTowers] [HasCountableProducts A.mateDerived]
    (l : StrictProjectionLimit A) (n : ℕᵒᵖ) :
    ev A l n ≅ ((CategoryTheory.evaluation ℕᵒᵖ A.mateModules).obj n).mapDerivedCategory :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A.projectionTowers (.up ℤ)) A.mateDerived).preimageIso
      (Functor.isoWhiskerRight l.evaluation
        (CategoryTheory.evaluation ℕᵒᵖ A.mateDerived |>.obj n) ≪≫
        ((CategoryTheory.evaluation ℕᵒᵖ A.mateModules).obj n).mapDerivedCategoryFactors.symm)

/-- The source comparison for evaluating the diagram-site mate.
Source: Stacks 0E48, 0A07
(blueprint: def-sbc-strict-coefficient-exchange-arrows). -/
def evaluatedSource {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (dg : StrictProjectionDirectImage g lT lS)
    (K : T.mateDerived) (n : ℕᵒᵖ) :
    (ev X lX n).obj (upper q dg K) ≅
      f.left.obj (g.right.obj ((ev T lT n).obj (input q K))) :=
  (evComparison X lX n).app (upper q dg K) ≪≫
    (leftEvaluation f n).app (dg.Rt.obj (input q K)) ≪≫
    f.left.mapIso ((evComparison S lS n).symm.app (dg.Rt.obj (input q K))) ≪≫
    f.left.mapIso ((Functor.isoWhiskerRight dg.evaluation
      (CategoryTheory.evaluation ℕᵒᵖ S.mateDerived |>.obj n)).app (input q K))

/-- The target comparison for evaluating the diagram-site mate.
Source: Stacks 0E48, 0A07
(blueprint: def-sbc-strict-coefficient-exchange-arrows). -/
def evaluatedTarget {s : RingedTensorSquare S T X Y g f e h}
    (q : Coefficients f g h e s) (dh : StrictProjectionDirectImage h lY lX)
    (K : T.mateDerived) (n : ℕᵒᵖ) :
    (ev X lX n).obj (lower q dh K) ≅
      h.right.obj (e.left.obj ((ev T lT n).obj (input q K))) :=
  (Functor.isoWhiskerRight dh.evaluation
    (CategoryTheory.evaluation ℕᵒᵖ X.mateDerived |>.obj n)).app ((towerLeft e).obj (input q K)) ≪≫
    h.right.mapIso ((evComparison Y lY n).app ((towerLeft e).obj (input q K))) ≪≫
    h.right.mapIso ((leftEvaluation e n).app (input q K)) ≪≫
    h.right.mapIso (e.left.mapIso ((evComparison T lT n).symm.app (input q K)))


end SheafOfModules.StrictQuotientExchange
