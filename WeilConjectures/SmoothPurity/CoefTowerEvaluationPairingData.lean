/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefTowerTraceData
public import WeilConjectures.AlgebraicGeometry.ScalarUnitRestrictionSingle
public import WeilConjectures.SmoothPurity.DualizingSupportEvaluation.DualizingSupportEvaluation
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

import Mathlib.CategoryTheory.Generator.Presheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory

/-! # Evaluation and compact support before taking inverse limits

Source: blueprint `prop-coef-integral-dualizing`, proof paragraph 2
(blueprint: lem-coef-tower-evaluation-pairing).
The index n denotes positive exponent n+1. The target is the already fixed
compact-support tower, before its trace. All constructions retain the tower index.

## Main definitions

- `coefPairingHom`, `coefPairingSupport`: the contravariant and covariant towers.
- `CoefPairingSystem.beta`: the adjunction-mate/evaluation composite before trace.
- `coefPairingFiniteBeta`: its ambient finite-level formula, including scalar balancing.

## Main statements

- `coefTowerEvaluationPairing`: representative computation, finite evaluation and dinaturality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MonoidalClosed.FunctorCategory
open SheafOfModules
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The strict module-tower category used by the fixed trace target.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
abbrev coefPairingModules := ℕᵒᵖ ⥤ ModuleCat.{u + 1} (coefTraceRing l E)

/-- The ordinary unbounded derived category of strict R-module towers.
Source: Stacks 0941 (blueprint: lem-coef-tower-evaluation-pairing). -/
abbrev coefPairingDerived := DerivedCategory (coefPairingModules l E)

/-- The derived tensor of towers, constructed by the existing K-flat localization.
Source: Stacks 06YY, 0941 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingTensor : coefPairingDerived l E × coefPairingDerived l E ⥤
    coefPairingDerived l E := MonoidalCategory.tensor _

/-- Sections after actual quotient-scalar restriction, retaining the strict tower.
Source: blueprint proof paragraph 2 (blueprint: lem-coef-tower-evaluation-pairing). -/
def coefPairingSections (W : Scheme.{u}) :
    coefficientSequenceDerived.{u, u} l E W ⥤ coefPairingDerived l E :=
  (coefTraceSystemRestriction l E W).mapDerivedCategory ⋙
    (coefTraceSections l E W).rightDerivedFunctor

end WeilConjectures

namespace CategoryTheory

universe b c d v₁ v₂ v₃ v₄

/-- The adjoint-evaluation construction used on both the sequence site and its finite
slices. The functors J, P, R and RX are supplied independently: exact open extension,
separately derived proper image, point sections and source sections, respectively.
No invertibility of a proper or sections projection mate is included.
Source: blueprint proof steps 5--8 (blueprint: lem-coef-tower-evaluation-pairing). -/
structure CoefPairingFrame
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B) (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (J : A ⥤ B) (P : B ⥤ C) (R : C ⥤ D) (RX : A ⥤ D) where
  /-- Derived restriction to the open subsite. -/
  jstar : B ⥤ A
  /-- Exact open extension is left adjoint to open restriction. -/
  openAdjunction : J ⊣ jstar
  /-- Derived pullback along the proper part. -/
  pstar : C ⥤ B
  /-- The ringed derived pullback/direct-image adjunction. -/
  properAdjunction : pstar ⊣ P
  /-- Derived extension of the constant base scalars after point pullback. -/
  sstar : D ⥤ C
  /-- Point sections, including scalar restriction, are its right adjoint. -/
  sectionsAdjunction : sstar ⊣ R
  /-- Pullback composition identifies source sections with this right adjoint. -/
  sourceAdjunction : sstar ⋙ pstar ⋙ jstar ⊣ RX
  /-- Canonical tensor pullback comparison along p. -/
  properTensor : TC ⋙ pstar ≅ pstar.prod pstar ⋙ TB
  /-- Canonical tensor pullback comparison along point sections and scalar extension. -/
  sectionsTensor : TD ⋙ sstar ≅ sstar.prod sstar ⋙ TC
  /-- Canonical tensor pullback along open restriction. -/
  restrictionTensor : TB ⋙ jstar ≅ jstar.prod jstar ⋙ TA
  /-- The inverse-open-projection arrow is the actual counit mate. -/
  openTensor : ∀ (L : B) (M : A), J.obj (TA.obj (jstar.obj L, M)) ≅ TB.obj (L, J.obj M)
  /-- Its adjunct is insertion into j* j!, following inverse tensor comparison. -/
  openTensor_adjunct : ∀ (L : B) (M : A),
    openAdjunction.homEquiv _ _ (openTensor L M).hom =
      TA.map (Prod.mkHom (𝟙 (jstar.obj L)) (openAdjunction.unit.app M)) ≫
        restrictionTensor.inv.app (L, J.obj M)

namespace CoefPairingFrame

variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {TA : A × A ⥤ A} {TB : B × B ⥤ B} {TC : C × C ⥤ C} {TD : D × D ⥤ D}
  {J : A ⥤ B} {P : B ⥤ C} {R : C ⥤ D} {RX : A ⥤ D}
  (F : CoefPairingFrame TA TB TC TD J P R RX)

/-- The left-oriented projection mate, obtained by transposing tensor of the counit.
It is the usual projection mate conjugated by the canonical graded symmetries.
Source: blueprint steps 7--8 (blueprint: lem-coef-tower-evaluation-pairing). -/
def leftMate {V : Type a} {W : Type b} [Category.{v₁} V] [Category.{v₂} W]
    (TV : V × V ⥤ V) (TW : W × W ⥤ W) (L : V ⥤ W) (G : W ⥤ V)
    (adj : L ⊣ G) (mu : TV ⋙ L ≅ L.prod L ⋙ TW) (H : V) (M : W) :
    TV.obj (H, G.obj M) ⟶ G.obj (TW.obj (L.obj H, M)) :=
  let flip := (Functor.flipping (C := V) (D := V) (E := W)).functor
  ((adj.rightAdjointProjectionMap
    (T_C := (Functor.curryObj TW).flip) (T_D := (Functor.curryObj TV).flip)
    (flip.map (Functor.curry.map mu.hom) ≫
      (flip.mapIso (Functor.curryObjProdComp L L TW)).hom)).app M).app H

/-- The composite of the point-sections mate, proper mate and open tensor inverse.
All three arrows live in the derived system categories before finite evaluation.
Source: blueprint steps 5--8 (blueprint: lem-coef-tower-evaluation-pairing). -/
def projection (H : D) (M : A) :
    TD.obj (H, R.obj (P.obj (J.obj M))) ⟶
      R.obj (P.obj (J.obj (TA.obj (F.jstar.obj (F.pstar.obj (F.sstar.obj H)), M)))) :=
  leftMate TD TC F.sstar R F.sectionsAdjunction F.sectionsTensor H (P.obj (J.obj M)) ≫
    R.map (leftMate TC TB F.pstar P F.properAdjunction F.properTensor
      (F.sstar.obj H) (J.obj M)) ≫
    R.map (P.map (F.openTensor (F.pstar.obj (F.sstar.obj H)) M).inv)

/-- Evaluation after the source-sections counit, followed by compact support.
This formula includes the scalar-balancing map through sstar. It ends at F(Q);
no exceptional counit or trace is composed into it.
Source: blueprint steps 6--8 (blueprint: lem-coef-tower-evaluation-pairing). -/
def pairing {HA : Aᵒᵖ × A ⥤ A} (S : WeilConjectures.CoefficientClosedStructure HA)
    (tensor_eq : S.tensor = TA) (M Q : A) :
    TD.obj (RX.obj (HA.obj (op M, Q)), R.obj (P.obj (J.obj M))) ⟶
      R.obj (P.obj (J.obj Q)) :=
  F.projection (RX.obj (HA.obj (op M, Q))) M ≫
    R.map (P.map (J.map
      (TA.map (Prod.mkHom (F.sourceAdjunction.counit.app (HA.obj (op M, Q))) (𝟙 M)) ≫
        eqToHom (congrArg (fun T ↦ T.obj (HA.obj (op M, Q), M)) tensor_eq.symm) ≫
          S.evaluation M Q)))

end CoefPairingFrame
end CategoryTheory

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Ordinary quotient-ring open extension and proper image, together with the actual
scalar-restriction comparisons. These are witnesses of the fixed ringed construction,
not hypotheses on K. The proper image is derived after open extension.
Source: blueprint steps 1 and 4--8 (blueprint: lem-coef-tower-evaluation-pairing). -/
structure CoefPairingSystem {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) (S : CoefficientDerivedSystemCalculus l E X) where
  /-- The existing K-flat tensor-Hom data on the compactification. -/
  compactTensors : CoefficientDerivedSystemTensors l E c.Z
  /-- The existing K-flat tensor-Hom data on the base. -/
  baseTensors : CoefficientDerivedSystemTensors l E Y
  /-- Exact module-sheaf extension by zero on the quotient sequence site. -/
  openModules : coefficientSequenceModules.{u, u} l E X ⥤
    coefficientSequenceModules.{u, u} l E c.Z
  /-- The separately derived ordinary module-sheaf direct image. -/
  properModules : coefficientSequenceModules.{u, u} l E c.Z ⥤
    coefficientSequenceModules.{u, u} l E Y
  [openAdditive : openModules.Additive]
  [openLimits : PreservesFiniteLimits openModules]
  [openColimits : PreservesFiniteColimits openModules]
  [properAdditive : properModules.Additive]
  /-- The underlying open operation is the recorded actual extension by zero. -/
  openRestriction : openModules ⋙ coefTraceSystemRestriction l E c.Z ≅
    coefTraceSystemRestriction l E X ⋙ coefTraceOpen l E c.i
  /-- The underlying proper operation is the recorded actual direct image. -/
  properRestriction : properModules ⋙ coefTraceSystemRestriction l E Y ≅
    coefTraceSystemRestriction l E c.Z ⋙ coefTracePush l E c.g
  /-- Ambient adjunctions, canonical pullback tensor comparisons and open tensor mate. -/
  frame : CoefPairingFrame S.systemClosed.tensor compactTensors.systemClosed.tensor
    baseTensors.systemClosed.tensor (coefPairingTensor l E)
    openModules.mapDerivedCategory properModules.rightDerivedFunctor
    (coefPairingSections l E Y) (coefPairingSections l E X)
  /-- The direct-image composition comparison after exact scalar restriction. -/
  compactSections : openModules.mapDerivedCategory ⋙ properModules.rightDerivedFunctor ⋙
    coefPairingSections l E Y ≅ coefTraceCompactSections l E c

attribute [instance] CoefPairingSystem.openAdditive CoefPairingSystem.openLimits
  CoefPairingSystem.openColimits CoefPairingSystem.properAdditive

variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

end WeilConjectures
