/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Paper.RingedTensorSquarePresentation
public import Sheaf.Paper.ProjectionMateExact
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import Sheaf.Paper.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Homology.Monoidal
import Sheaf.Paper.ringedProjectionFormula_totalization_left
import all Sheaf.Paper.ProjectionFormulaArrows
import all Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionGeneral
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck

/-!
# Projection morphisms of augmented strict derived towers

Source: Stacks Project, Cohomology on Sites, Tags 0943 and 0A07; Algebraization,
Tag 0A0G (blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism).

All tower objects below belong to the localization of the abelian category of
strict towers. Evaluation is a functor out of that localization, not an equivalence
with towers in the derived category. The chain models and their localization
factorizations retain arbitrary representatives and all coefficient transitions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u w uI vI uB vB uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite


namespace SheafOfModules

/-- Strict module towers on the recorded ringed site.
Source: Stacks 0A07 (blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
abbrev RingedTensorCorner.projectionTowers (A : RingedTensorCorner.{u, w}) :=
  ℕᵒᵖ ⥤ A.mateModules

/-- The bounded finite-free condition on an augmented strict coefficient tower.
Bounds may depend on the level, and rank zero is allowed.
Source: Stacks 0943, 0A0G
(blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
def RingedTensorCorner.projectionCoefficientProperty (A : RingedTensorCorner.{u, w}) :
    ObjectProperty (Under ((Functor.const ℕᵒᵖ).obj A.mateUnitComplex)) :=
  fun P ↦ ∀ n : ℕᵒᵖ,
    (∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero ((P.right.obj n).X r)) ∧
    (∀ r : ℤ, ∃ k : ℕ,
      Nonempty ((P.right.obj n).X r ≅
        ∏ᶜ fun _ : Fin k ↦ unit ((sheafCompose A.topology
          (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring)))

/-- Augmented strict bounded finite-free towers, with all augmentation-preserving chain maps.
Source: Stacks 0943, 0A0G
(blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
abbrev RingedTensorCorner.projectionCoefficients (A : RingedTensorCorner.{u, w}) :=
  A.projectionCoefficientProperty.FullSubcategory

/-- Forget the augmentation and bounded finite-free property, retaining the entire diagram.
Source: Stacks 0943 (blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
def RingedTensorCorner.projectionCoefficientDiagram (A : RingedTensorCorner.{u, w}) :
    A.projectionCoefficients ⥤ (ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ) :=
  A.projectionCoefficientProperty.ι ⋙ Under.forget _

/-- The direct-sum total tensor bifunctor of the recorded module category.
Source: Stacks 0943 (blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
abbrev RingedTensorCorner.projectionTotal (A : RingedTensorCorner.{u, w}) :=
  A.mateTensor.map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- Tensor every coefficient level, functorially in the complex and the whole coefficient tower.
Source: Stacks 0943 (blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
def RingedTensorCorner.projectionTensorDiagrams (A : RingedTensorCorner.{u, w}) :=
  A.projectionTotal ⋙
    Functor.whiskeringRight ℕᵒᵖ (CochainComplex A.mateModules ℤ)
      (CochainComplex A.mateModules ℤ) ⋙
    (Functor.whiskeringLeft A.projectionCoefficients
      (ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ)
      (ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ)).obj A.projectionCoefficientDiagram

/-- The termwise-pulled-back coefficient diagram; its maps are the pulled-back chain maps.
Source: Stacks 0943 (blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
def RingedTensorEdge.projectionCoefficientDiagram
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X) :=
  Y.projectionCoefficientDiagram ⋙
    (Functor.whiskeringRight ℕᵒᵖ (CochainComplex Y.mateModules ℤ)
      (CochainComplex X.mateModules ℤ)).obj
        (e.pullback.mapHomologicalComplex (ComplexShape.up ℤ))

/-- The X-side total tensors with the pulled-back coefficient tower.
Source: Stacks 0943 (blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
def RingedTensorEdge.projectionTensorDiagrams
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X) :=
  X.projectionTotal ⋙
    Functor.whiskeringRight ℕᵒᵖ (CochainComplex X.mateModules ℤ)
      (CochainComplex X.mateModules ℤ) ⋙
    (Functor.whiskeringLeft Y.projectionCoefficients
      (ℕᵒᵖ ⥤ CochainComplex X.mateModules ℤ)
      (ℕᵒᵖ ⥤ CochainComplex X.mateModules ℤ)).obj e.projectionCoefficientDiagram

/-- Postcomposition on diagrams, retaining the original functor and natural transformations.
Source: Stacks 0A07 (blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
abbrev projectionPost {I : Type uI} {B : Type uB} {D : Type uD}
    [Category.{vI} I] [Category.{vB} B] [Category.{vD} D] (F : B ⥤ D) :=
  (Functor.whiskeringRight I B D).obj F

/-- The derived limit, evaluation, and Roos data for an abelian category of strict towers.
Source: Stacks 0A07, 0940, 0941
(blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
structure StrictProjectionLimitData (B : Type uB) [Category.{vB} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ B]
    {DB DT : Type*} [Category* DB] [Category* DT]
    [HasZeroObject DB] [HasShift DB ℤ] [Preadditive DB]
    [∀ n : ℤ, (shiftFunctor DB n).Additive] [Pretriangulated DB]
    [HasCountableProducts DB]
    (Q : CochainComplex B ℤ ⥤ DB) (QT : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ DT)
    [QT.IsLocalization (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ))] where
  L : DT ⥤ DB
  eta : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex
    (ComplexShape.up ℤ) ⋙ Q ⟶ QT ⋙ L
  ev : DT ⥤ (ℕᵒᵖ ⥤ DB)
  evaluation : QT ⋙ ev ≅
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ projectionPost Q
  p : ∀ Z, L.obj Z ⟶ ∏ᶜ fun n : ℕ ↦ (ev.obj Z).obj (op n)
  delta : ∀ Z, (∏ᶜ fun n : ℕ ↦ (ev.obj Z).obj (op n)) ⟶ (L.obj Z)⟦(1 : ℤ)⟧
  derived : L.IsRightDerivedFunctor eta
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (ComplexShape.up ℤ))
  computes : ∀ I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ, I.IsKInjective → IsIso (eta.app I)
  roos : ∀ Z, IsDerivedLimitTriangle
    (fun n : ℕ ↦ (ev.obj Z).map (homOfLE (Nat.le_succ n)).op) (L.obj Z) (p Z) (delta Z)
  p_natural : ∀ {Z W} (v : Z ⟶ W),
    L.map v ≫ p W = p Z ≫ Limits.Pi.map (fun n : ℕ ↦ (ev.map v).app (op n))
  delta_natural : ∀ {Z W} (v : Z ⟶ W),
    Limits.Pi.map (fun n : ℕ ↦ (ev.map v).app (op n)) ≫ delta W =
      delta Z ≫ (L.map v)⟦(1 : ℤ)⟧'

/-- The total right derived inverse limit with its comparison, evaluation and Roos triangle.
This is precisely the data supplied by the strict-tower homotopy-limit dependency.
Source: Stacks 0A07, 0940, 0941
(blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
abbrev StrictProjectionLimit (A : RingedTensorCorner.{u, w})
    [HasDerivedCategory.{w} A.projectionTowers]
    [HasCountableProducts A.mateDerived] :=
  StrictProjectionLimitData A.mateModules DerivedCategory.Q DerivedCategory.Q

/-- Levelwise module direct image and its action on complexes of strict towers.
Source: Stacks 0A07 (blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
abbrev RingedTensorEdge.projectionTowerPushforward
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X) :=
  (Functor.whiskeringRight ℕᵒᵖ X.mateModules Y.mateModules).obj e.pushforward

/-- Normalized total derived direct image on strict towers, over abstract abelian categories.
The counit normalization is retained as the specified predicate on the derived comparison.
Source: Stacks 0A07, 0940
(blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
structure StrictProjectionDirectImageData
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasLimitsOfShape ℕᵒᵖ D]
    {DB DD TB TD : Type*} [Category* DB] [Category* DD] [Category* TB] [Category* TD]
    [HasZeroObject DB] [HasShift DB ℤ] [Preadditive DB]
    [∀ n : ℤ, (shiftFunctor DB n).Additive] [Pretriangulated DB]
    [HasZeroObject DD] [HasShift DD ℤ] [Preadditive DD]
    [∀ n : ℤ, (shiftFunctor DD n).Additive] [Pretriangulated DD]
    [HasCountableProducts DB] [HasCountableProducts DD]
    (QY : CochainComplex B ℤ ⥤ DB) (QX : CochainComplex D ℤ ⥤ DD)
    (QTY : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ TB)
    (QTX : CochainComplex (ℕᵒᵖ ⥤ D) ℤ ⥤ TD)
    [QX.IsLocalization (HomologicalComplex.quasiIso D (.up ℤ))]
    [QTY.IsLocalization (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ))]
    [QTX.IsLocalization (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ D) (.up ℤ))]
    (V : D ⥤ B) [V.Additive] (R : DD ⥤ DB)
    (lx : StrictProjectionLimitData D QX QTX) (ly : StrictProjectionLimitData B QY QTY)
    (CounitNormalized : (V.mapHomologicalComplex (.up ℤ) ⋙ QY ⟶ QX ⋙ R) → Prop) where
  eta : V.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ QY ⟶
    QX ⋙ R
  Rt : TD ⥤ TB
  towerEta : (projectionPost V).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    QTY ⟶ QTX ⋙ Rt
  evaluation : Rt ⋙ ly.ev ≅ lx.ev ⋙ projectionPost R
  ordinary : (lim : (ℕᵒᵖ ⥤ D) ⥤ D) ⋙ V ≅
    (projectionPost V) ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B)
  a : lx.L ⋙ R ≅ Rt ⋙ ly.L
  derived : R.IsRightDerivedFunctor eta
    (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
  computes : ∀ I : CochainComplex D ℤ, I.IsKInjective → IsIso (eta.app I)
  counit_normalized : CounitNormalized eta
  towerDerived : Rt.IsRightDerivedFunctor towerEta
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ D) (ComplexShape.up ℤ))
  towerComputes : ∀ I : CochainComplex (ℕᵒᵖ ⥤ D) ℤ,
    I.IsKInjective → IsIso (towerEta.app I)
  evaluation_normalized : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ D) ℤ), I.IsKInjective →
    ∀ n : ℕᵒᵖ,
      (ly.ev.map (towerEta.app I)).app n ≫
          (evaluation.hom.app (QTX.obj I)).app n ≫
          R.map ((lx.evaluation.hom.app I).app n) =
        (ly.evaluation.hom.app
          (((projectionPost V).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).app n ≫
          eta.app (I.asFunctor.obj n)
  ordinary_normalized : ∀ H, ordinary.hom.app H = limit.post H V
  normalized : ∀ I : CochainComplex (ℕᵒᵖ ⥤ D) ℤ,
    eta.app (((lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) ≫ R.map (lx.eta.app I) ≫
        a.hom.app (QTX.obj I) =
      QY.map ((NatTrans.mapHomologicalComplex ordinary.hom
        (ComplexShape.up ℤ)).app I) ≫
        ly.eta.app (((projectionPost V).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≫ ly.L.map (towerEta.app I)

/-- The prescribed ordinary-counit normalization of the derived direct-image comparison.
Source: Stacks 0943 (blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
def RingedTensorEdge.ProjectionCounitNormalized
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X) [e.pushforward.Additive]
    (eta : e.pushforward.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ e.right) : Prop :=
  ∀ I : CochainComplex X.mateModules ℤ, I.IsKInjective →
          e.left.map (eta.app I) ≫ e.derivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
            derivedPullbackComplexComparison e.pullback e.left e.epsilon
              ((e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
            DerivedCategory.Q.map
              ((e.moduleAdjunction.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I)

/-- The common-direct-image comparison, with its underived normalization.
This packages the specified comparison of the pushforward/limit dependency, not an
arbitrary isomorphism. Evaluation is normalized on K-injective tower complexes.
Source: Stacks 0A07, 0940
(blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
abbrev StrictProjectionDirectImage {Y X : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge Y X) [e.pushforward.Additive]
    [HasDerivedCategory.{w} X.projectionTowers]
    [HasDerivedCategory.{w} Y.projectionTowers]
    [HasCountableProducts X.mateDerived] [HasCountableProducts Y.mateDerived]
    (lx : StrictProjectionLimit X) (ly : StrictProjectionLimit Y) :=
  StrictProjectionDirectImageData DerivedCategory.Q DerivedCategory.Q
    DerivedCategory.Q DerivedCategory.Q e.pushforward e.right lx ly
    e.ProjectionCounitNormalized

/-- The canonical right unitor of total tensor, using Mathlib's signed total complex.
Source: Stacks 0943 (blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
def RingedTensorCorner.projectionRightUnitor (A : RingedTensorCorner.{u, w})
    (N : CochainComplex A.mateModules ℤ) :
    (A.projectionTotal.obj N).obj A.mateUnitComplex ≅ N :=
  letI := monoidalCategory A.ring
  letI := ringedTensorPreadditive A.ring
  HomologicalComplex.rightUnitor N

/-- The uniquely normalized ordinary pullback of the coefficient ring.
Source: Stacks 0943, 03EL
(blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
def RingedTensorEdge.projectionUnit {Y X : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge Y X) :=
  Classical.choose (canonicalRingedTensorComparison_unit Y.ring X.ring e.inverseRing
    e.inverse e.algebraic e.ringMap e.pullback e.object_eq e.map_eq e.ordinaryTensor).exists

/-- Termwise pullback of the degree-zero ring, with its canonical scalar-extension unit.
Source: Stacks 0943 (blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
def RingedTensorEdge.projectionUnitComplex {Y X : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge Y X) :
    (e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj Y.mateUnitComplex ≅
      X.mateUnitComplex :=
  (HomologicalComplex.singleMapHomologicalComplex e.pullback (ComplexShape.up ℤ) 0).app
      (unit ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)) ≪≫
    (CochainComplex.singleFunctor X.mateModules 0).mapIso e.projectionUnit

/-- A tensor tower's coaugmentation is the ordinary-limit lift of 1 tensor z.
The equations specify the actual chain map on every limit projection, before deriving.
Source: Stacks 0943, 0A07 (blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
def ProjectionCoaugmentation {A : RingedTensorCorner.{u, w}}
    (N : CochainComplex A.mateModules ℤ) (P : ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ)
    (z : (Functor.const ℕᵒᵖ).obj A.mateUnitComplex ⟶ P)
    (C : CochainComplex A.projectionTowers ℤ)
    (c : C.asFunctor ≅ P ⋙ A.projectionTotal.obj N)
    (i : N ⟶ ((lim : A.projectionTowers ⥤ A.mateModules).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C) : Prop :=
  ∀ (n : ℕᵒᵖ) (r : ℤ),
    i.f r ≫ limit.π (C.X r) n ≫ (c.hom.app n).f r =
      ((A.projectionRightUnitor N).inv ≫ (A.projectionTotal.obj N).map (z.app n)).f r

private def towerProjectionResult
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X)
    [e.pushforward.Additive]
    [HasDerivedCategory.{w} X.projectionTowers]
    [HasDerivedCategory.{w} Y.projectionTowers]
    [HasCountableProducts X.mateDerived] [HasCountableProducts Y.mateDerived]
    (lx : StrictProjectionLimit X) (ly : StrictProjectionLimit Y)
    (d : StrictProjectionDirectImage e lx ly) : Prop :=
    ∃ (CY : CochainComplex Y.mateModules ℤ ⥤
        Y.projectionCoefficients ⥤ CochainComplex Y.projectionTowers ℤ)
      (CX : CochainComplex X.mateModules ℤ ⥤
        Y.projectionCoefficients ⥤ CochainComplex X.projectionTowers ℤ)
      (cy : CY ⋙ projectionPost HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
        Y.projectionTensorDiagrams)
      (cx : CX ⋙ projectionPost HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
        e.projectionTensorDiagrams)
      (S : Y.mateDerived ⥤ Y.projectionCoefficients ⥤ DerivedCategory Y.projectionTowers)
      (T : X.mateDerived ⥤ Y.projectionCoefficients ⥤ DerivedCategory X.projectionTowers)
      (s : DerivedCategory.Q ⋙ S ≅ CY ⋙ projectionPost DerivedCategory.Q)
      (t : DerivedCategory.Q ⋙ T ≅ CX ⋙ projectionPost DerivedCategory.Q)
      (hf : ∀ (P : Y.projectionCoefficients) (n : ℕᵒᵖ),
        Y.mateFlat (P.obj.right.obj n) ∧
          X.mateFlat ((e.projectionCoefficientDiagram.obj P).obj n))
      (sEv : ∀ (M : Y.mateDerived) (P : Y.projectionCoefficients) (n : ℕᵒᵖ),
        Y.tensor.obj (M, DerivedCategory.Q.obj (P.obj.right.obj n)) ≅
          (ly.ev.obj ((S.obj M).obj P)).obj n)
      (tEv : ∀ (E : X.mateDerived) (P : Y.projectionCoefficients) (n : ℕᵒᵖ),
        X.tensor.obj (E, e.left.obj (DerivedCategory.Q.obj (P.obj.right.obj n))) ≅
          (lx.ev.obj ((T.obj E).obj P)).obj n)
      (u : e.right ⋙ S ⟶ T ⋙ projectionPost d.Rt)
      (zY : ∀ P : Y.projectionCoefficients, 𝟭 Y.mateDerived ⟶ (S.flip.obj P) ⋙ ly.L)
      (zX : ∀ P : Y.projectionCoefficients, 𝟭 X.mateDerived ⟶ (T.flip.obj P) ⋙ lx.L),
      (∀ (N : CochainComplex Y.mateModules ℤ) (P : Y.projectionCoefficients) (n : ℕᵒᵖ),
        (sEv (DerivedCategory.Q.obj N) P n).hom ≫
            (ly.ev.map ((s.hom.app N).app P)).app n ≫
            (ly.evaluation.hom.app ((CY.obj N).obj P)).app n ≫
            DerivedCategory.Q.map (((cy.hom.app N).app P).app n) =
          (mixedTensorRepresentative Y.ring Y.mateFlat (fun _ ↦ Iff.rfl)
            Y.tensor a.representative N (P.obj.right.obj n) (hf P n).1).hom) ∧
      (∀ (K : CochainComplex X.mateModules ℤ) (P : Y.projectionCoefficients) (n : ℕᵒᵖ),
        (tEv (DerivedCategory.Q.obj K) P n).hom ≫
            (lx.ev.map ((t.hom.app K).app P)).app n ≫
            (lx.evaluation.hom.app ((CX.obj K).obj P)).app n ≫
            DerivedCategory.Q.map (((cx.hom.app K).app P).app n) =
          X.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj K))
            (derivedPullbackComplexComparison e.pullback e.left e.epsilon
              (P.obj.right.obj n))) ≫
          (mixedTensorRepresentative X.ring X.mateFlat (fun _ ↦ Iff.rfl)
            X.tensor b.representative K ((e.projectionCoefficientDiagram.obj P).obj n)
              (hf P n).2).hom) ∧
      (∀ (P : Y.projectionCoefficients) (n : ℕᵒᵖ) {M M' : Y.mateDerived} (g : M ⟶ M'),
        Y.tensor.map (Prod.mkHom g (𝟙 (DerivedCategory.Q.obj (P.obj.right.obj n)))) ≫
            (sEv M' P n).hom =
          (sEv M P n).hom ≫ (ly.ev.map ((S.map g).app P)).app n) ∧
      (∀ (P : Y.projectionCoefficients) (n : ℕᵒᵖ) {E E' : X.mateDerived} (g : E ⟶ E'),
        X.tensor.map (Prod.mkHom g
            (𝟙 (e.left.obj (DerivedCategory.Q.obj (P.obj.right.obj n))))) ≫
            (tEv E' P n).hom =
          (tEv E P n).hom ≫ (lx.ev.map ((T.map g).app P)).app n) ∧
      (∀ (E : X.mateDerived) (P : Y.projectionCoefficients) (n : ℕᵒᵖ),
        (sEv (e.right.obj E) P n).hom ≫
            (ly.ev.map ((u.app E).app P)).app n ≫
            (d.evaluation.hom.app ((T.obj E).obj P)).app n =
          derivedProjectionFormulaMate e.left e.right e.derivedAdjunction Y.tensor X.tensor
            (e.tensorComparison a b) E (DerivedCategory.Q.obj (P.obj.right.obj n)) ≫
              e.right.map (tEv E P n).hom) ∧
      (∀ (N : CochainComplex Y.mateModules ℤ) (P : Y.projectionCoefficients),
        ∃ i : N ⟶ ((lim : Y.projectionTowers ⥤ Y.mateModules).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((CY.obj N).obj P),
          ProjectionCoaugmentation N P.obj.right P.obj.hom ((CY.obj N).obj P)
            ((Functor.mapIso ((CategoryTheory.evaluation Y.projectionCoefficients _).obj P)
              (cy.app N))) i ∧
          (zY P).app (DerivedCategory.Q.obj N) ≫ ly.L.map ((s.hom.app N).app P) =
            DerivedCategory.Q.map i ≫ ly.eta.app ((CY.obj N).obj P)) ∧
      (∀ (K : CochainComplex X.mateModules ℤ) (P : Y.projectionCoefficients),
        ∃ (z : (Functor.const ℕᵒᵖ).obj X.mateUnitComplex ⟶
            e.projectionCoefficientDiagram.obj P)
          (i : K ⟶ ((lim : X.projectionTowers ⥤ X.mateModules).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((CX.obj K).obj P)),
          (∀ n : ℕᵒᵖ, z.app n = e.projectionUnitComplex.inv ≫
            (e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).map (P.obj.hom.app n)) ∧
          ProjectionCoaugmentation K (e.projectionCoefficientDiagram.obj P) z
            ((CX.obj K).obj P)
            ((Functor.mapIso ((CategoryTheory.evaluation Y.projectionCoefficients _).obj P)
              (cx.app K))) i ∧
          (zX P).app (DerivedCategory.Q.obj K) ≫ lx.L.map ((t.hom.app K).app P) =
            DerivedCategory.Q.map i ≫ lx.eta.app ((CX.obj K).obj P)) ∧
      (∀ (E : X.mateDerived) (P : Y.projectionCoefficients),
        (zY P).app (e.right.obj E) ≫ ly.L.map ((u.app E).app P) =
          e.right.map ((zX P).app E) ≫ d.a.hom.app ((T.obj E).obj P)) ∧
      (∀ (E : X.mateDerived) (P : Y.projectionCoefficients),
        ly.L.map ((u.app E).app P) ≫ ly.p (d.Rt.obj ((T.obj E).obj P)) =
          ly.p ((S.obj (e.right.obj E)).obj P) ≫
            Limits.Pi.map (fun n : ℕ ↦ (ly.ev.map ((u.app E).app P)).app (op n))) ∧
      (∀ (E : X.mateDerived) (P : Y.projectionCoefficients),
        Limits.Pi.map (fun n : ℕ ↦ (ly.ev.map ((u.app E).app P)).app (op n)) ≫
            towerTransitionEndomorphism (fun n : ℕ ↦
              (ly.ev.obj (d.Rt.obj ((T.obj E).obj P))).map
                (homOfLE (Nat.le_succ n)).op) =
          towerTransitionEndomorphism (fun n : ℕ ↦
            (ly.ev.obj ((S.obj (e.right.obj E)).obj P)).map
              (homOfLE (Nat.le_succ n)).op) ≫
            Limits.Pi.map (fun n : ℕ ↦ (ly.ev.map ((u.app E).app P)).app (op n))) ∧
      (∀ (E : X.mateDerived) (P : Y.projectionCoefficients),
        Limits.Pi.map (fun n : ℕ ↦ (ly.ev.map ((u.app E).app P)).app (op n)) ≫
            ly.delta (d.Rt.obj ((T.obj E).obj P)) =
          ly.delta ((S.obj (e.right.obj E)).obj P) ≫
            (ly.L.map ((u.app E).app P))⟦(1 : ℤ)⟧')

open MonoidalCategory in
private theorem tensorComplexHasTotal
    {C : Type uB} [Category.{vB} C] [Preadditive C] [MonoidalCategory C]
    [MonoidalPreadditive C] [HasCoproducts.{0} C] :
    ∀ (K L : CochainComplex C ℤ),
      HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (.up ℤ) := by
  intro K L
  infer_instance

section ProjectionProof
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] DerivedCategory.Q
attribute [local irreducible] HomologicalComplex₂.total HomologicalComplex.mapBifunctorMap
attribute [local irreducible] CochainComplex.kInjectiveResolutionFunctor
  CochainComplex.toKInjectiveResolution

private def reassembleComplexes
    {I : Type uI} [Category.{vI} I] {B : Type uB} [Category.{vB} B]
    [HasZeroMorphisms B] :
    (I ⥤ CochainComplex B ℤ) ⥤ CochainComplex (I ⥤ B) ℤ :=
  HomologicalComplex.functorEquivalence.inverse B (.up ℤ) I

private def rawTensorDiagrams
    {B : Type uB} [Category.{vB} B] [HasZeroMorphisms B]
    {J : Type uI} [Category.{vI} J]
    (T : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (P : J ⥤ ℕᵒᵖ ⥤ CochainComplex B ℤ) :=
  T ⋙ Functor.whiskeringRight ℕᵒᵖ (CochainComplex B ℤ) (CochainComplex B ℤ) ⋙
    (Functor.whiskeringLeft J (ℕᵒᵖ ⥤ CochainComplex B ℤ)
      (ℕᵒᵖ ⥤ CochainComplex B ℤ)).obj P

private theorem existsComplexDiagrams
    {B : Type uB} [Category.{vB} B] [Preadditive B]
    {J : Type uI} [Category.{vI} J] {K : Type*} [Category* K]
    (D : K ⥤ J ⥤ ℕᵒᵖ ⥤ CochainComplex B ℤ) :
    ∃ C : K ⥤ J ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
      Nonempty (C ⋙ projectionPost
        HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅ D) := by
  let e := ((HomologicalComplex.functorEquivalence B (.up ℤ) ℕᵒᵖ).congrRight
    (E := J)).congrRight (E := K)
  exact ⟨e.inverse.obj D, ⟨e.counitIso.app D⟩⟩

private def diagramEvaluationIso
    {B : Type uB} [Category.{vB} B] [HasZeroMorphisms B]
    {J : Type uI} [Category.{vI} J] {K : Type*} [Category* K]
    (C : K ⥤ J ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (D : K ⥤ J ⥤ ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (c : C ⋙ projectionPost
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅ D)
    (p : J) (n : ℕᵒᵖ) :
    C.flip.obj p ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (CochainComplex B ℤ)).obj n ≅
      D.flip.obj p ⋙ (CategoryTheory.evaluation ℕᵒᵖ (CochainComplex B ℤ)).obj n := by
  refine NatIso.ofComponents (fun k ↦
    ((CategoryTheory.evaluation ℕᵒᵖ (CochainComplex B ℤ)).obj n).mapIso
      (((CategoryTheory.evaluation J _).obj p).mapIso (c.app k))) ?_
  intro k k' f
  exact congr_app (congr_app (c.hom.naturality f) p) n

private def comparisonLevelIso
    {B : Type uB} [Category.{vB} B] [HasZeroMorphisms B]
    {J : Type uI} [Category.{vI} J]
    (T : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (P : J ⥤ ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (C : CochainComplex B ℤ ⥤ J ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (c : C ⋙ projectionPost
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅ rawTensorDiagrams T P)
    (p : J) (n : ℕᵒᵖ) :
    C.flip.obj p ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (CochainComplex B ℤ)).obj n ≅
      T.flip.obj ((P.obj p).obj n) := by
  refine NatIso.ofComponents (fun k ↦
    ((CategoryTheory.evaluation ℕᵒᵖ (CochainComplex B ℤ)).obj n).mapIso
      (((CategoryTheory.evaluation J _).obj p).mapIso (c.app k))) ?_
  intro k k' f
  exact congr_app (congr_app (c.hom.naturality f) p) n

private def comparisonTowerIso
    {B : Type uB} [Category.{vB} B] [HasZeroMorphisms B]
    {J : Type uI} [Category.{vI} J]
    (T : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (P : J ⥤ ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (C : CochainComplex B ℤ ⥤ J ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (c : C ⋙ projectionPost
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅ rawTensorDiagrams T P)
    (p : J) :
    C.flip.obj p ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
      T ⋙ (Functor.whiskeringLeft ℕᵒᵖ
        (CochainComplex B ℤ) (CochainComplex B ℤ)).obj (P.obj p) := by
  refine NatIso.ofComponents
    (fun k ↦ ((CategoryTheory.evaluation J _).obj p).mapIso (c.app k)) ?_
  intro k k' f
  exact congr_app (c.hom.naturality f) p

private theorem descendComplexDiagrams
    (B : Type uB) [Category.{vB} B] [Abelian B]
    {DB DT : Type*} [Category* DB] [Category* DT]
    (Q : CochainComplex B ℤ ⥤ DB) (QT : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ DT)
    [Q.IsLocalization (HomologicalComplex.quasiIso B (.up ℤ))]
    [QT.IsLocalization (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ))]
    {J : Type uI} [Category.{vI} J]
    (C : CochainComplex B ℤ ⥤ J ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (D : CochainComplex B ℤ ⥤ J ⥤ ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (c : C ⋙ projectionPost
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅ D)
    (hD : ∀ {K K' : CochainComplex B ℤ} (f : K ⟶ K'), QuasiIso f →
      ∀ (P : J) (n : ℕᵒᵖ), QuasiIso (((D.map f).app P).app n)) :
    ∃ S : DB ⥤ J ⥤ DT,
      Nonempty (Q ⋙ S ≅ C ⋙ projectionPost QT) := by
  let F := C ⋙ projectionPost QT
  have hF : (HomologicalComplex.quasiIso B (ComplexShape.up ℤ)).IsInvertedBy F := by
    intro K K' f hf
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro P
    apply Localization.inverts QT (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ))
    apply (HomologicalComplex.quasiIso_iff_evaluation _).2
    intro n
    change QuasiIso ((C.flip.obj P ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (CochainComplex B ℤ)).obj n).map f)
    let a := diagramEvaluationIso C D c P n
    apply (quasiIso_iff_comp_right _ (a.hom.app K')).1
    rw [a.hom.naturality f]
    have := hD f hf P n
    change QuasiIso (a.hom.app K ≫ ((D.map f).app P).app n)
    infer_instance
  exact ⟨Localization.lift F hF Q,
    ⟨Localization.fac F hF Q⟩⟩

private def tensorDiagramMate
    {A : Type uB} [Category.{vB} A] [HasZeroMorphisms A]
    {B : Type uD} [Category.{vD} B] [HasZeroMorphisms B]
    {J : Type uI} [Category.{vI} J]
    (H : CochainComplex B ℤ ⥤ CochainComplex A ℤ)
    (L : CochainComplex A ℤ ⥤ CochainComplex B ℤ)
    (TY : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TX : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (P : J ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (tc : H ⋙ TY ⟶ (Functor.postcompose₂.obj H).obj
      ((((Functor.whiskeringLeft₂ (CochainComplex B ℤ)).obj
        (𝟭 (CochainComplex B ℤ))).obj L).obj TX)) :
    H ⋙ rawTensorDiagrams TY P ⟶
      rawTensorDiagrams TX (P ⋙ projectionPost L) ⋙ projectionPost (projectionPost H) where
  app K :=
    { app := fun p ↦
        { app := fun n ↦ (tc.app K).app ((P.obj p).obj n)
          naturality := fun n m f ↦ (tc.app K).naturality ((P.obj p).map f) }
      naturality := by
        intro p p' f
        apply NatTrans.ext
        funext n
        exact (tc.app K).naturality ((P.map f).app n) }
  naturality K K' f := by
    apply NatTrans.ext
    funext p
    apply NatTrans.ext
    funext n
    exact congr_app (tc.naturality f) ((P.obj p).obj n)

private theorem liftDiagramMorphism
    {A : Type uB} [Category.{vB} A] [HasZeroMorphisms A]
    {B : Type uD} [Category.{vD} B] [HasZeroMorphisms B]
    {J : Type uI} [Category.{vI} J]
    {C D : Type*} [Category* C] [Category* D]
    (V : B ⥤ A) [V.PreservesZeroMorphisms]
    [((Functor.whiskeringRight ℕᵒᵖ B A).obj V).PreservesZeroMorphisms] (H : C ⥤ D)
    (CY : D ⥤ J ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (CX : C ⥤ J ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (DY : D ⥤ J ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (DX : C ⥤ J ⥤ ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (cy : CY ⋙ projectionPost
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅ DY)
    (cx : CX ⋙ projectionPost
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅ DX)
    (σ : H ⋙ DY ⟶ DX ⋙ projectionPost
      (projectionPost (V.mapHomologicalComplex (.up ℤ)))) :
    ∃ τ : H ⋙ CY ⟶ CX ⋙ projectionPost
        ((projectionPost V).mapHomologicalComplex (.up ℤ)),
      ∀ k p n,
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
          ((τ.app k).app p)).app n) ≫
            (V.mapHomologicalComplex (.up ℤ)).map (((cx.hom.app k).app p).app n) =
          (((cy.hom.app (H.obj k)).app p).app n) ≫ (((σ.app k).app p).app n) := by
  let VC := V.mapHomologicalComplex (.up ℤ)
  let σ' : H ⋙ CY ⋙ projectionPost
        HomologicalComplex.complexOfFunctorsToFunctorToComplex ⟶
      CX ⋙ projectionPost HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        projectionPost (projectionPost VC) :=
    Functor.whiskerLeft H cy.hom ≫ σ ≫
      Functor.whiskerRight cx.inv (projectionPost (projectionPost VC))
  let τ : H ⋙ CY ⟶ CX ⋙ projectionPost
      ((projectionPost V).mapHomologicalComplex (.up ℤ)) :=
    { app := fun k ↦
        { app := fun p ↦
            { f := fun r ↦
                { app := fun n ↦ (((σ'.app k).app p).app n).f r
                  naturality := fun n m f ↦
                    HomologicalComplex.congr_hom (((σ'.app k).app p).naturality f) r }
              comm' := fun r s _ ↦ by
                apply NatTrans.ext
                funext n
                exact (((σ'.app k).app p).app n).comm r s }
          naturality := by
            intro p p' f
            apply HomologicalComplex.Hom.ext
            funext r
            apply NatTrans.ext
            funext n
            exact HomologicalComplex.congr_hom
              (congr_app ((σ'.app k).naturality f) n) r }
      naturality := by
        intro k k' f
        apply NatTrans.ext
        funext p
        apply HomologicalComplex.Hom.ext
        funext r
        apply NatTrans.ext
        funext n
        exact HomologicalComplex.congr_hom
          (congr_app (congr_app (σ'.naturality f) p) n) r }
  refine ⟨τ, ?_⟩
  intro k p n
  have he : (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      ((τ.app k).app p)).app n = ((σ'.app k).app p).app n := by
    apply HomologicalComplex.Hom.ext
    funext r
    rfl
  rw [he]
  have hc : ((cx.inv.app k).app p).app n ≫ ((cx.hom.app k).app p).app n = 𝟙 _ := by
    exact congr_app (congr_app (cx.inv_hom_id_app k) p) n
  change (_ ≫ _ ≫ VC.map (((cx.inv.app k).app p).app n)) ≫
    VC.map (((cx.hom.app k).app p).app n) = _
  simp only [Category.assoc, ← VC.map_comp, hc, VC.map_id, Category.comp_id]
  rfl

private theorem transportChainSquare
    {A B : Type*} [Category* A] [Category* B] (V : B ⥤ A)
    {D E : A} {X Y : B} (a : V.obj X ⟶ D) (cy : D ⟶ E)
    (b : X ⟶ Y) {Z : B} (cx : Y ⟶ Z) (τ : D ⟶ V.obj Y)
    (tc : E ⟶ V.obj Z) (y : V.obj X ⟶ E) (x : X ⟶ Z)
    [Mono (V.map cx)] (hy : a ≫ cy = y) (hx : b ≫ cx = x)
    (ht : τ ≫ V.map cx = cy ≫ tc) (hu : y ≫ tc = V.map x) :
    a ≫ τ = V.map b := by
  apply (cancel_mono (V.map cx)).1
  rw [Category.assoc, ht, ← Category.assoc, hy, hu, ← V.map_comp, hx]

private theorem transportEvaluationSquare
    {A B : Type*} [Category* A] [Category* B] (R : B ⥤ A)
    {U V W W' : A} {X Y Z : B} (θ : U ⟶ V) (cc : V ⟶ R.obj X)
    (ev : X ⟶ Y) (cx : Y ⟶ Z) (h : U ⟶ W)
    (q : W ⟶ W') (δ₀ : W ⟶ R.obj Y) (δ₁ : W' ⟶ R.obj Z)
    (hθ : θ ≫ cc ≫ R.map ev = h ≫ δ₀)
    (hc : δ₀ ≫ R.map cx = q ≫ δ₁) :
    θ ≫ cc ≫ R.map (ev ≫ cx) = (h ≫ q) ≫ δ₁ := by
  calc
    _ = (θ ≫ cc ≫ R.map ev) ≫ R.map cx := by
      rw [R.map_comp]
      simp only [Category.assoc]
    _ = (h ≫ δ₀) ≫ R.map cx := congrArg (fun z ↦ z ≫ R.map cx) hθ
    _ = (h ≫ q) ≫ δ₁ := by rw [Category.assoc, hc, Category.assoc]

private theorem transportNaturalitySquare
    {A B : Type*} [Category* A] [Category* B] (Q : B ⥤ A)
    {U V : A} {X Y Z W : B} (σ : U ⟶ V) (ey : U ⟶ Q.obj X)
    (ex : V ⟶ Q.obj Y) (τ : X ⟶ Y) (cy : X ⟶ Z) (cx : Y ⟶ W)
    (tc : Z ⟶ W) (h : σ ≫ ex = ey ≫ Q.map τ)
    (ht : τ ≫ cx = cy ≫ tc) :
    σ ≫ (ex ≫ Q.map cx) = (ey ≫ Q.map cy) ≫ Q.map tc := by
  rw [← Category.assoc, h, Category.assoc, ← Q.map_comp, ht,
    Q.map_comp, Category.assoc]

private theorem chooseFamily
    {I : Type*} {A : I → Type*} {P : ∀ i, A i → Prop}
    (h : ∀ i, ∃ a, P i a) : ∃ f : ∀ i, A i, ∀ i, P i (f i) := by
  classical
  choose f hf using h
  exact ⟨f, hf⟩

private theorem chooseFamilies
    {I : Type*} {J : I → Type*} {A : ∀ i, J i → Type*}
    {P : ∀ i j, A i j → Prop} (h : ∀ i j, ∃ a, P i j a) :
    ∃ f : ∀ i j, A i j, ∀ i j, P i j (f i j) := by
  classical
  choose f hf using h
  exact ⟨f, hf⟩


private theorem prependNormalization
    {C : Type*} [Category* C] {A B D E F G : C}
    (f : A ⟶ B) (a : B ⟶ D) (b : D ⟶ E) (c : E ⟶ F) (d : F ⟶ G)
    (r : B ⟶ G) (h : a ≫ b ≫ c ≫ d = r)
    {x : A ⟶ D} (hx : x = f ≫ a) : x ≫ b ≫ c ≫ d = f ≫ r := by
  rw [hx, Category.assoc, h]

private theorem cancelProjectionLifting
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {A B U : D} {X Y : C} (sh : A ⟶ B) (si : B ⟶ A)
    (th : X ⟶ Y) (ti : Y ⟶ X) (hs : sh ≫ si = 𝟙 A) (ht : ti ≫ th = 𝟙 Y)
    (a : A ⟶ U) (u : U ⟶ R.obj X) (b : B ⟶ R.obj Y)
    (h : (si ≫ a) ≫ u = b ≫ R.map ti) :
    a ≫ u ≫ R.map th = sh ≫ b := by
  have h' := congrArg (fun v ↦ sh ≫ v ≫ R.map th) h
  simp only [← Category.assoc, hs, Category.id_comp] at h'
  simpa only [Category.assoc, ← R.map_comp, ht, R.map_id, Category.comp_id] using h'

private theorem liftViaResolution
    {B : Type uB} [Category.{vB} B] {D : Type uD} [Category.{vD} D]
    {J : Type uI} [Category.{vI} J]
    (Q : B ⥤ D) (W : MorphismProperty B) [Q.IsLocalization W]
    (R : B ⥤ B) (i : 𝟭 B ⟶ R)
    (hi : ∀ K, IsIso (Q.map (i.app K)))
    (F G : D ⥤ J) (H : B ⥤ J) (α : H ⟶ Q ⋙ F)
    (hα : ∀ K, IsIso (α.app (R.obj K))) (τ : H ⟶ Q ⋙ G) :
    ∃ u : F ⟶ G, ∀ K, α.app K ≫ u.app (Q.obj K) = τ.app K := by
  have hqi : IsIso (Functor.whiskerRight i Q) :=
    (NatTrans.isIso_iff_isIso_app _).2 hi
  have ha : IsIso (Functor.whiskerLeft R α) :=
    (NatTrans.isIso_iff_isIso_app _).2 hα
  let qi : Q ≅ R ⋙ Q := asIso (Functor.whiskerRight i Q)
  let a : R ⋙ H ≅ R ⋙ Q ⋙ F := asIso (Functor.whiskerLeft R α)
  let β : Q ⋙ F ⟶ Q ⋙ G :=
    (Functor.isoWhiskerRight qi F).hom ≫ a.inv ≫ Functor.whiskerLeft R τ ≫
      (Functor.isoWhiskerRight qi G).inv
  let ff := Localization.fullyFaithfulWhiskeringLeft Q W J
  let u := ff.preimage β
  refine ⟨u, ?_⟩
  intro K
  have hu := congr_app (ff.map_preimage β) K
  change u.app (Q.obj K) = β.app K at hu
  rw [hu]
  apply (cancel_mono (G.map (Q.map (i.app K)))).1
  dsimp only [β, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [qi, a, asIso_hom, asIso_inv, NatIso.isIso_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.assoc, ← G.map_comp, IsIso.inv_hom_id,
    G.map_id]
  have hαnat : H.map (i.app K) ≫ α.app (R.obj K) =
      α.app K ≫ F.map (Q.map (i.app K)) := α.naturality (i.app K)
  have hτnat : H.map (i.app K) ≫ τ.app (R.obj K) =
      τ.app K ≫ G.map (Q.map (i.app K)) := τ.naturality (i.app K)
  rw [← Category.assoc, ← Category.assoc, ← hαnat]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  exact (congrArg (fun v ↦ H.map (i.app K) ≫ v) (Category.comp_id _)).trans hτnat

private def coefficientIso
    {A B T U J : Type*} [Category* A] [Category* B] [Category* T]
    [Category* U] [Category* J]
    (Q : A ⥤ B) (QT : T ⥤ U) (S : B ⥤ J ⥤ U) (C : A ⥤ J ⥤ T)
    (s : Q ⋙ S ≅ C ⋙ projectionPost QT) (p : J) :
    Q ⋙ S.flip.obj p ≅ C.flip.obj p ⋙ QT := by
  refine NatIso.ofComponents
    (fun a ↦ ((CategoryTheory.evaluation J U).obj p).mapIso (s.app a)) ?_
  intro a a' f
  exact congr_app (s.hom.naturality f) p

private def postDiagramTransformation
    {TX TY DX DY J : Type*} [Category* TX] [Category* TY]
    [Category* DX] [Category* DY] [Category* J]
    (F : TX ⥤ TY) (QY : TY ⥤ DY) (QX : TX ⥤ DX) (R : DX ⥤ DY)
    (θ : F ⋙ QY ⟶ QX ⋙ R) :
    projectionPost (I := J) F ⋙ projectionPost QY ⟶
      projectionPost QX ⋙ projectionPost R where
  app H :=
    { app := fun p ↦ θ.app (H.obj p)
      naturality := fun _ _ f ↦ θ.naturality (H.map f) }
  naturality _ _ g := by
    apply NatTrans.ext
    funext p
    exact θ.naturality (g.app p)

private theorem liftNormalizedProjection
    {B A TX TY D E DX DY : Type*}
    [Category* B] [Category* A] [Category* TX] [Category* TY]
    [Category* D] [Category* E] [Category* DX] [Category* DY]
    (QB : B ⥤ D) (W : MorphismProperty B) [QB.IsLocalization W]
    (QA : A ⥤ E) (QX : TX ⥤ DX) (QY : TY ⥤ DY)
    (V : B ⥤ A) (R : D ⥤ E) (δ : V ⋙ QA ⟶ QB ⋙ R)
    (CX : B ⥤ TX) (CY : A ⥤ TY) (F : TX ⥤ TY)
    (S : E ⥤ DY) (T : D ⥤ DX) (Rt : DX ⥤ DY)
    (s : QA ⋙ S ≅ CY ⋙ QY) (t : QB ⋙ T ≅ CX ⋙ QX)
    (σ : V ⋙ CY ⟶ CX ⋙ F) (θ : F ⋙ QY ⟶ QX ⋙ Rt)
    (RI : B ⥤ B) (ι : 𝟭 B ⟶ RI) (hι : ∀ K, IsIso (QB.map (ι.app K)))
    (hδ : ∀ K, IsIso (δ.app (RI.obj K))) :
    ∃ u : R ⋙ S ⟶ T ⋙ Rt, ∀ K,
      S.map (δ.app K) ≫ u.app (QB.obj K) ≫ Rt.map (t.hom.app K) =
        s.hom.app (V.obj K) ≫ QY.map (σ.app K) ≫ θ.app (CX.obj K) := by
  let α : V ⋙ CY ⋙ QY ⟶ QB ⋙ R ⋙ S :=
    Functor.whiskerLeft V s.inv ≫ Functor.whiskerRight δ S
  let β : V ⋙ CY ⋙ QY ⟶ QB ⋙ T ⋙ Rt :=
    Functor.whiskerRight σ QY ≫ Functor.whiskerLeft CX θ ≫ Functor.whiskerRight t.inv Rt
  have hα (K : B) : IsIso (α.app (RI.obj K)) := by
    have := hδ K
    change IsIso (s.inv.app (V.obj (RI.obj K)) ≫ S.map (δ.app (RI.obj K)))
    infer_instance
  obtain ⟨u, hu⟩ := liftViaResolution QB W RI ι hι (R ⋙ S) (T ⋙ Rt)
    (V ⋙ CY ⋙ QY) α hα β
  refine ⟨u, ?_⟩
  intro K
  exact cancelProjectionLifting Rt (s.hom.app (V.obj K)) (s.inv.app (V.obj K))
    (t.hom.app K) (t.inv.app K) (s.hom_inv_id_app _) (t.inv_hom_id_app _) _ _ _
    (by simpa only [α, β, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc] using hu K)

section
attribute [local irreducible] monoidalCategory mixedTensorRepresentative



private theorem naturalOfResolutions
    {B : Type uB} [Category.{vB} B] [Abelian B]
    {D : Type uD} [Category.{vD} D]
    (PR : ObjectProperty (CochainComplex B ℤ)) (G T : CochainComplex B ℤ ⥤ D)
    (b : ∀ P, PR P → (G.obj P ≅ T.obj P))
    (hb : ∀ P P' (hP : PR P) (hP' : PR P') (f : P ⟶ P'),
      G.map f ≫ (b P' hP').hom = (b P hP).hom ≫ T.map f)
    (z : ∀ K, G.obj K ≅ T.obj K)
    (hz : ∀ K P (hP : PR P) (p : P ⟶ K), QuasiIso p →
      G.map p ≫ (z K).hom = (b P hP).hom ≫ T.map p)
    (hres : ∀ K, ∃ (P : CochainComplex B ℤ) (_hP : PR P) (p : P ⟶ K),
      QuasiIso p ∧ Epi p)
    (hG : ∀ {K K'} (p : K ⟶ K'), QuasiIso p → IsIso (G.map p))
    {K K' : CochainComplex B ℤ} (f : K ⟶ K') :
    G.map f ≫ (z K').hom = (z K).hom ≫ T.map f := by
  obtain ⟨P, hP, p, hp, he⟩ := hres K'
  have := hp
  have := he
  obtain ⟨W, hW, q, hq, _⟩ := hres (Limits.pullback p f)
  have := hq
  have hs := CategoryTheory.quasiIso_pullback_snd p f
  let v : W ⟶ K := q ≫ pullback.snd p f
  let w : W ⟶ P := q ≫ pullback.fst p f
  have hv : QuasiIso v := by dsimp [v]; infer_instance
  have hw : v ≫ f = w ≫ p := by
    simp only [v, w, Category.assoc, pullback.condition]
  have := hG v hv
  apply (cancel_epi (G.map v)).1
  calc
    G.map v ≫ (G.map f ≫ (z K').hom) =
        G.map w ≫ (G.map p ≫ (z K').hom) := by
      rw [← Category.assoc, ← G.map_comp, hw, G.map_comp, Category.assoc]
    _ = G.map w ≫ ((b P hP).hom ≫ T.map p) := by rw [hz K' P hP p hp]
    _ = (b W hW).hom ≫ T.map (w ≫ p) := by
      rw [← Category.assoc, hb W P hW hP w, Category.assoc, ← T.map_comp]
    _ = (b W hW).hom ≫ T.map (v ≫ f) := by rw [hw]
    _ = G.map v ≫ ((z K).hom ≫ T.map f) := by
      rw [T.map_comp, ← Category.assoc, ← hz K W hW v hv, Category.assoc]

private theorem representativeFirstNaturality
    {C : Type uB} [Category.{vB} C] {D : Type uD} [Category.{vD} D]
    (Q : C ⥤ D) (T : C ⥤ C ⥤ C) (U : D × D ⥤ D) (P : ObjectProperty C)
    (r : (P.ι.prod P.ι) ⋙ Functor.uncurry.obj T ⋙ Q ≅
      ((P.ι ⋙ Q).prod (P.ι ⋙ Q)) ⋙ U)
    (K K' F : P.FullSubcategory) (f : K ⟶ K') :
    U.map (Prod.mkHom (Q.map f.hom) (𝟙 (Q.obj F.obj))) ≫ (r.app (K', F)).inv =
      (r.app (K, F)).inv ≫ Q.map ((T.map f.hom).app F.obj) := by
  have h := r.inv.naturality (Prod.mkHom f (𝟙 F))
  simpa only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    ObjectProperty.ι_obj, ObjectProperty.ι_map, Functor.uncurry_obj_map,
    ObjectProperty.FullSubcategory.id_hom, CategoryTheory.Functor.map_id,
    Category.comp_id, Iso.app_inv] using h

private theorem resolutionTensorNatIso
    {B : Type uB} [Category.{vB} B] [Abelian B]
    {D : Type uD} [Category.{vD} D]
    (Q : CochainComplex B ℤ ⥤ D)
    (T : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (U : D × D ⥤ D) (PR : ObjectProperty (CochainComplex B ℤ))
    (r : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj T ⋙ Q ≅
      ((PR.ι ⋙ Q).prod (PR.ι ⋙ Q)) ⋙ U)
    (F : CochainComplex B ℤ) (hF : PR F)
    (mixed : ∀ K, U.obj (Q.obj K, Q.obj F) ≅ Q.obj ((T.obj K).obj F))
    (hm : ∀ K P (hP : PR P) (p : P ⟶ K), QuasiIso p →
      U.map (Prod.mkHom (Q.map p) (𝟙 (Q.obj F))) ≫ (mixed K).hom =
        (r.app (⟨P, hP⟩, ⟨F, hF⟩)).inv ≫ Q.map ((T.map p).app F))
    (hres : ∀ K, ∃ (P : CochainComplex B ℤ) (_hP : PR P) (p : P ⟶ K),
      QuasiIso p ∧ Epi p)
    (hinv : ∀ {K K'} (p : K ⟶ K'), QuasiIso p → IsIso (Q.map p)) :
    ∃ m : Q ⋙ (Functor.curryObj U).flip.obj (Q.obj F) ≅ T.flip.obj F ⋙ Q,
      ∀ K, m.hom.app K = (mixed K).hom := by
  let G := Q ⋙ (Functor.curryObj U).flip.obj (Q.obj F)
  let H := T.flip.obj F ⋙ Q
  let b (P : CochainComplex B ℤ) (hP : PR P) : G.obj P ≅ H.obj P :=
    (r.app (⟨P, hP⟩, ⟨F, hF⟩)).symm
  have hb (P P' : CochainComplex B ℤ) (hP : PR P) (hP' : PR P') (f : P ⟶ P') :
      G.map f ≫ (b P' hP').hom = (b P hP).hom ≫ H.map f :=
    representativeFirstNaturality Q T U PR r ⟨P, hP⟩ ⟨P', hP'⟩ ⟨F, hF⟩
      (ObjectProperty.homMk f)
  refine ⟨NatIso.ofComponents mixed ?_, fun _ ↦ rfl⟩
  intro K K' f
  refine naturalOfResolutions PR G H b hb mixed hm hres ?_ f
  intro K K' p hp
  have := hinv p hp
  change IsIso (U.map (Prod.mkHom (Q.map p) (𝟙 (Q.obj F))))
  have : IsIso (Prod.mkHom (Q.map p) (𝟙 (Q.obj F))) :=
    (isIso_prod_iff _ _).2 ⟨by assumption, by infer_instance⟩
  infer_instance

private theorem mixedTensorNatIso (A : RingedTensorCorner.{u, w}) (a : RingedTensorModel A)
    (F : CochainComplex A.mateModules ℤ) (hF : A.mateFlat F) :
    ∃ m : DerivedCategory.Q.{w} ⋙ (Functor.curryObj A.tensor).flip.obj
        (DerivedCategory.Q.{w}.obj F) ≅
      A.projectionTotal.flip.obj F ⋙ DerivedCategory.Q.{w},
      ∀ K, m.hom.app K = (mixedTensorRepresentative A.ring A.mateFlat
        (fun _ ↦ Iff.rfl) A.tensor a.representative K F hF).hom := by
  -- Cache the direct additive parent of the existing sheaf abelian instance.
  let : Abelian A.mateModules :=
    { (inferInstance : Abelian A.mateModules) with
      toPreadditive := (inferInstance : Preadditive A.mateModules) }
  let : ∀ K L : CochainComplex A.mateModules ℤ,
      HomologicalComplex.HasMapBifunctor K L A.mateTensor (.up ℤ) :=
    @tensorComplexHasTotal A.mateModules _ _ (monoidalCategory A.ring)
      (ringedTensorPreadditive A.ring) _
  refine resolutionTensorNatIso DerivedCategory.Q.{w} A.projectionTotal A.tensor
    A.mateFlat a.representative F hF
    (fun K ↦ mixedTensorRepresentative A.ring A.mateFlat (fun _ ↦ Iff.rfl)
      A.tensor a.representative K F hF) ?_ ?_ ?_
  · intro K P hP p hp
    unfold mixedTensorRepresentative
    exact (Classical.choose_spec (mixedTensorRepresentative_existsUnique A.ring
      A.mateFlat (fun _ ↦ Iff.rfl) A.tensor a.representative K F hF).exists) P hP p hp
  · intro K
    obtain ⟨P, p, hk, ht, hq, he⟩ := CochainComplex.exists_isKFlatResolutionGeneral K
    exact ⟨P, ⟨hk, ht⟩, p, hq, HomologicalComplex.epi_of_epi_f p he⟩
  · intro K K' p hp
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso A.mateModules p).2 hp
private theorem descendEvaluationIso
    {B : Type uB} [Category.{vB} B] {D : Type uD} [Category.{vD} D]
    {E : Type uI} [Category.{vI} E]
    (Q : B ⥤ D) (W : MorphismProperty B) [Q.IsLocalization W]
    (F G : D ⥤ E) (H : B ⥤ E) (m : Q ⋙ F ≅ H) (r : Q ⋙ G ≅ H) :
    ∃ e : F ≅ G, ∀ K, e.hom.app (Q.obj K) ≫ r.hom.app K = m.hom.app K := by
  let ff := Localization.fullyFaithfulWhiskeringLeft Q W E
  let b := m ≪≫ r.symm
  let e := ff.preimageIso b
  refine ⟨e, ?_⟩
  intro K
  have he := congr_app (ff.map_preimage b.hom) K
  change e.hom.app (Q.obj K) = m.hom.app K ≫ r.inv.app K at he
  rw [he, Category.assoc, r.inv_hom_id_app, Category.comp_id]

private def evaluationPostIso
    {I : Type uI} [Category.{vI} I] {B : Type uB} [Category.{vB} B]
    {D : Type uD} [Category.{vD} D] (Q : B ⥤ D) (n : I) :
    projectionPost (I := I) Q ⋙ (CategoryTheory.evaluation I D).obj n ≅
      (CategoryTheory.evaluation I B).obj n ⋙ Q := Iso.refl _

private def levelComparisonIso
    {I C D E F : Type*} [Category* I] [Category* C] [Category* D]
    [Category* E] [Category* F]
    (R : E ⥤ F) (V : C ⥤ D) (G : D ⥤ I ⥤ F) (H : C ⥤ I ⥤ E)
    (e : V ⋙ G ≅ H ⋙ projectionPost R) (n : I) :
    V ⋙ G ⋙ (CategoryTheory.evaluation I F).obj n ≅
      H ⋙ (CategoryTheory.evaluation I E).obj n ⋙ R := by
  refine NatIso.ofComponents
    (fun K ↦ ((CategoryTheory.evaluation I F).obj n).mapIso (e.app K)) ?_
  intro K K' f
  exact congr_app (e.hom.naturality f) n

private theorem evaluatedLocalizationIso
    {B : Type uB} [Category.{vB} B] {D : Type uD} [Category.{vD} D]
    {I : Type uI} [Category.{vI} I]
    {BT : Type*} [Category* BT] {DT : Type*} [Category* DT]
    (Q : B ⥤ D) (W : MorphismProperty B) [Q.IsLocalization W]
    (QT : BT ⥤ DT) (ev : DT ⥤ I ⥤ D) (R : BT ⥤ I ⥤ B)
    (evIso : QT ⋙ ev ≅ R ⋙ projectionPost Q)
    (C : B ⥤ BT) (S : D ⥤ DT) (s : Q ⋙ S ≅ C ⋙ QT)
    (n : I) (H : B ⥤ B) (F : D ⥤ D)
    (c : C ⋙ R ⋙ (CategoryTheory.evaluation I B).obj n ≅ H)
    (mixed : ∀ K : B, F.obj (Q.obj K) ≅ Q.obj (H.obj K))
    (norm : ∃ m : Q ⋙ F ≅ H ⋙ Q, ∀ K, m.hom.app K = (mixed K).hom) :
    ∃ e : F ≅ S ⋙ ev ⋙ (CategoryTheory.evaluation I D).obj n, ∀ K,
      e.hom.app (Q.obj K) ≫ (ev.map (s.hom.app K)).app n ≫
        (evIso.hom.app (C.obj K)).app n ≫ Q.map (c.hom.app K) = (mixed K).hom := by
  obtain ⟨m, hm⟩ := norm
  let e₀ := Functor.isoWhiskerRight s ev ≪≫ Functor.isoWhiskerLeft C evIso
  let ed := (CategoryTheory.evaluation I D).obj n
  let r : Q ⋙ S ⋙ ev ⋙ ed ≅ H ⋙ Q :=
    Functor.isoWhiskerRight e₀ ed ≪≫
      Functor.isoWhiskerLeft (C ⋙ R) (evaluationPostIso Q n) ≪≫
        Functor.isoWhiskerRight c Q
  obtain ⟨e, he⟩ := descendEvaluationIso Q W F (S ⋙ ev ⋙ ed) (H ⋙ Q) m r
  refine ⟨e, ?_⟩
  intro K
  have h := he K
  dsimp only [r, e₀, ed, evaluationPostIso, Iso.refl_hom, NatTrans.id_app,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  simp only [CategoryTheory.evaluation_obj_map] at h
  erw [Category.id_comp] at h
  calc
    _ = m.hom.app K := by simpa only [NatTrans.comp_app, Category.assoc] using h
    _ = _ := hm K


private theorem diagramTensorEvaluation
    (B : Type uB) [Category.{vB} B] [Abelian B]
    {DB DT : Type*} [Category* DB] [Category* DT]
    (Q : CochainComplex B ℤ ⥤ DB) (QT : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ DT)
    [Q.IsLocalization (HomologicalComplex.quasiIso B (.up ℤ))]
    [QT.IsLocalization (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ))]
    {J : Type uI} [Category.{vI} J]
    (ev : DT ⥤ ℕᵒᵖ ⥤ DB)
    (evIso : QT ⋙ ev ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ projectionPost Q)
    (T : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (P : J ⥤ ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (C : CochainComplex B ℤ ⥤ J ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (S : DB ⥤ J ⥤ DT)
    (s : Q ⋙ S ≅ C ⋙ projectionPost QT)
    (c : C ⋙ projectionPost
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅ rawTensorDiagrams T P)
    (p : J) (n : ℕᵒᵖ) (F : DB ⥤ DB)
    (mixed : ∀ K, F.obj (Q.obj K) ≅
      Q.obj ((T.obj K).obj ((P.obj p).obj n)))
    (norm : ∃ m : Q ⋙ F ≅
        T.flip.obj ((P.obj p).obj n) ⋙ Q,
      ∀ K, m.hom.app K = (mixed K).hom) :
    ∃ e : F ≅ S.flip.obj p ⋙ ev ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (DB)).obj n,
      ∀ K, e.hom.app (Q.obj K) ≫
          (ev.map ((s.hom.app K).app p)).app n ≫
          (evIso.hom.app ((C.obj K).obj p)).app n ≫
          Q.map (((c.hom.app K).app p).app n) = (mixed K).hom := by
  exact evaluatedLocalizationIso Q
    (HomologicalComplex.quasiIso B (.up ℤ)) QT
    ev HomologicalComplex.complexOfFunctorsToFunctorToComplex evIso
    (C.flip.obj p) (S.flip.obj p)
    (coefficientIso Q QT S C s p) n
    (T.flip.obj ((P.obj p).obj n)) F
    (comparisonLevelIso T P C c p n) mixed norm


end

private def mapAugmentation
    {I : Type uI} [Category.{vI} I] {C : Type uB} [Category.{vB} C]
    {D : Type uD} [Category.{vD} D] (F : C ⥤ D) {U : C} {V : D}
    (j : F.obj U ≅ V) {P : I ⥤ C} (z : (Functor.const I).obj U ⟶ P) :
    (Functor.const I).obj V ⟶ P ⋙ F where
  app n := j.inv ≫ F.map (z.app n)
  naturality n m f := by
    have hz : z.app m = z.app n ≫ P.map f :=
      (Category.id_comp (z.app m)).symm.trans (z.naturality f)
    exact (Category.id_comp _).trans
      ((congrArg (fun v ↦ j.inv ≫ F.map v) hz).trans
        ((congrArg (fun v ↦ j.inv ≫ v) (F.map_comp (z.app n) (P.map f))).trans
          (Category.assoc _ _ _).symm))

private theorem tensorMapQuasiIso (A : RingedTensorCorner.{u, w})
    (F : CochainComplex A.mateModules ℤ) (hF : A.mateFlat F)
    {K K' : CochainComplex A.mateModules ℤ} (f : K ⟶ K') (hf : QuasiIso f) :
    QuasiIso ((A.projectionTotal.map f).app F) := by
  let := monoidalCategory A.ring
  let := ringedTensorPreadditive A.ring
  exact CategoryTheory.tensor_quasiIso_of_acyclicTensor F hF.1 f hf

private theorem coefficientFlat (A : RingedTensorCorner.{u, w})
    (P : A.projectionCoefficients) (n : ℕᵒᵖ) :
    A.mateFlat (P.obj.right.obj n) := by
  classical
  let F := P.obj.right.obj n
  let j (r : ℤ) := Classical.choice ((P.property n).2 r).choose_spec
  let pkg : StrictPerfectCoefficientPackage
      ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring) F :=
    { N := fun r ↦ ((P.property n).2 r).choose
      i := fun r ↦ (j r).hom
      p := fun r ↦ (j r).inv
      splitting := fun r ↦ (j r).hom_inv_id }
  exact StrictPerfectCoefficientPackage.isKFlat_flat A.ring F pkg (P.property n).1

private theorem projectionRightUnitorNaturality
    (A : RingedTensorCorner.{u, w}) {N N' : CochainComplex A.mateModules ℤ} (f : N ⟶ N') :
    f ≫ (A.projectionRightUnitor N').inv =
      (A.projectionRightUnitor N).inv ≫ (A.projectionTotal.map f).app A.mateUnitComplex := by
  let := monoidalCategory A.ring
  let := ringedTensorPreadditive A.ring
  let := symmetricCategory A.ring
  let := SheafOfModules.monoidalClosed (R := A.ring)
  exact MonoidalCategory.rightUnitor_inv_naturality f

attribute [local irreducible] RingedTensorCorner.projectionRightUnitor

private theorem towerCoaugmentation
    (B : Type uB) [Category.{vB} B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]
    (T : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (U : CochainComplex B ℤ) (ρ : ∀ N, (T.obj N).obj U ≅ N)
    (hρ : ∀ {N N' : CochainComplex B ℤ} (f : N ⟶ N'),
      f ≫ (ρ N').inv = (ρ N).inv ≫ (T.map f).app U)
    (P : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (z : (Functor.const ℕᵒᵖ).obj U ⟶ P)
    (C : CochainComplex B ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (c : C ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
      T ⋙ (Functor.whiskeringLeft ℕᵒᵖ
        (CochainComplex B ℤ) (CochainComplex B ℤ)).obj P) :
    ∃ i : 𝟭 (CochainComplex B ℤ) ⟶ C ⋙
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (ComplexShape.up ℤ),
      ∀ N n r, (i.app N).f r ≫ limit.π ((C.obj N).X r) n ≫
        ((c.hom.app N).app n).f r = ((ρ N).inv ≫ (T.obj N).map (z.app n)).f r := by
  let β : (Functor.const ℕᵒᵖ : CochainComplex B ℤ ⥤ _) ⟶
      T ⋙ (Functor.whiskeringLeft ℕᵒᵖ
        (CochainComplex B ℤ) (CochainComplex B ℤ)).obj P :=
    { app := fun N ↦
        { app := fun n ↦ (ρ N).inv ≫
            (T.obj N).map (z.app n)
          naturality := by
            intro n m f
            have hz : z.app m = z.app n ≫ P.map f := by simpa using z.naturality f
            change 𝟙 N ≫ _ = _ ≫ (T.obj N).map (P.map f)
            rw [Category.id_comp, Category.assoc, ← (T.obj N).map_comp, ← hz] }
      naturality := by
        intro N N' f
        apply NatTrans.ext; funext n
        change f ≫ ((ρ N').inv ≫
            (T.obj N').map (z.app n)) =
          ((ρ N).inv ≫ (T.obj N).map (z.app n)) ≫
            (T.map f).app (P.obj n)
        erw [← Category.assoc, hρ, Category.assoc,
          ← (T.map f).naturality (z.app n), ← Category.assoc] }
  let h : (Functor.const ℕᵒᵖ : B ⥤ (ℕᵒᵖ ⥤ B)).mapHomologicalComplex
      (ComplexShape.up ℤ) ⟶ C :=
    Functor.whiskerRight (β ≫ c.inv) reassembleComplexes
  have : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive :=
    Functor.additive_of_preserves_binary_products _
  let adj := CategoryTheory.Adjunction.mapHomologicalComplex (ComplexShape.up ℤ)
    (constLimAdj : (Functor.const ℕᵒᵖ : B ⥤ (ℕᵒᵖ ⥤ B)) ⊣ lim)
  let i : 𝟭 (CochainComplex B ℤ) ⟶ C ⋙
      (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (ComplexShape.up ℤ) :=
    adj.unit ≫ Functor.whiskerRight h
      ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ))
  refine ⟨i, ?_⟩
  intro N n r
  have he := (adj.homEquiv N (C.obj N)).symm_apply_apply (h.app N)
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_unit] at he
  have he' := congrArg (fun v ↦ (v.f r).app n) he
  change (i.app N).f r ≫ limit.π ((C.obj N).X r) n = ((h.app N).f r).app n at he'
  rw [← Category.assoc, he']
  change (((β.app N) ≫ c.inv.app N).app n).f r ≫ ((c.hom.app N).app n).f r = _
  rw [← HomologicalComplex.comp_f]
  have hc := congr_app (c.inv_hom_id_app N) n
  change (c.inv.app N).app n ≫ (c.hom.app N).app n = 𝟙 _ at hc
  simp only [NatTrans.comp_app, Category.assoc, hc, Category.comp_id]
  rfl


private theorem diagramCoaugmentation
    (B : Type uB) [Category.{vB} B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]
    {J : Type uI} [Category.{vI} J]
    (T : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (U : CochainComplex B ℤ) (ρ : ∀ N, (T.obj N).obj U ≅ N)
    (hρ : ∀ {N N' : CochainComplex B ℤ} (f : N ⟶ N'),
      f ≫ (ρ N').inv = (ρ N).inv ≫ (T.map f).app U)
    (P : J ⥤ ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (C : CochainComplex B ℤ ⥤ J ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (c : C ⋙ projectionPost
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅ rawTensorDiagrams T P)
    (p : J) (z : (Functor.const ℕᵒᵖ).obj U ⟶ P.obj p) :
    ∃ i : 𝟭 (CochainComplex B ℤ) ⟶ C.flip.obj p ⋙
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ),
      ∀ N n r, (i.app N).f r ≫ limit.π (((C.obj N).obj p).X r) n ≫
        (((c.hom.app N).app p).app n).f r =
          ((ρ N).inv ≫ (T.obj N).map (z.app n)).f r := by
  exact towerCoaugmentation B T U ρ hρ (P.obj p) z
    (C.flip.obj p) (comparisonTowerIso T P C c p)

private theorem pullbackPreservesFlat
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (F : CochainComplex Y.mateModules ℤ) (hF : Y.mateFlat F) :
    X.mateFlat ((e.pullback.mapHomologicalComplex (.up ℤ)).obj F) := by
  let := monoidalCategory Y.ring
  let := monoidalCategory X.ring
  have hf (n : ℤ) : IsFlatOnSite (J := Y.topology) (R := Y.ring) (F.X n) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso Y.ring _).symm (hF.2 n)
  obtain ⟨hk, ht⟩ := isKFlat_ringedToposPullback e.inverse e.direct e.adjunction
    e.algebraic e.ringMap e.pullback e.object_eq e.map_eq F
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat F).2 hF.1) hf
  refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hk, ?_⟩
  intro n
  exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso X.ring _) (ht n)

private theorem pullbackFlatComputes
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (P : CochainComplex Y.mateModules ℤ) (hP : Y.mateFlat P) :
    IsIso (derivedPullbackComplexComparison e.pullback e.left e.epsilon P) := by
  obtain ⟨L₀, ε₀, h₀, _, _, hc, _⟩ := ringedTopoiDerivedPullback
    e.inverse e.direct e.adjunction e.algebraic e.ringMap e.pullback e.object_eq e.map_eq
  have := h₀
  have := e.isLeftDerived
  let W := HomotopyCategory.quasiIso Y.mateModules (.up ℤ)
  let c := Functor.leftDerivedUnique L₀ e.left e.epsilon ε₀ W
  let K := (HomotopyCategory.quotient Y.mateModules (ComplexShape.up ℤ)).obj P
  have h := Functor.leftDerivedNatTrans_app e.left L₀ e.epsilon ε₀ W
    (Iso.refl _).hom K
  have heq : c.hom.app (DerivedCategory.Qh.obj K) ≫ ε₀.app K = e.epsilon.app K := by
    simpa only [c, Functor.leftDerivedNatIso_hom, Iso.refl_hom, NatTrans.id_app,
      Category.comp_id] using h
  have hε : IsIso (ε₀.app K) := hc P hP.1 hP.2
  have : IsIso (e.epsilon.app K) := by
    rw [← heq]
    infer_instance
  dsimp only [derivedPullbackComplexComparison]
  infer_instance

private theorem descendCoaugmentation
    {B : Type uB} [Category.{vB} B] {D : Type uD} [Category.{vD} D]
    {E : Type uI} [Category.{vI} E] {E' : Type*} [Category* E']
    (Q : B ⥤ D) (W : MorphismProperty B) [Q.IsLocalization W]
    (Q' : E ⥤ E') (C : B ⥤ E) (S : D ⥤ E')
    (R : E ⥤ B) (L : E' ⥤ D) (η : R ⋙ Q ⟶ Q' ⋙ L)
    (s : Q ⋙ S ≅ C ⋙ Q') (i : 𝟭 B ⟶ C ⋙ R) :
    ∃ z : 𝟭 D ⟶ S ⋙ L, ∀ K,
      z.app (Q.obj K) ≫ L.map (s.hom.app K) = Q.map (i.app K) ≫ η.app (C.obj K) := by
  let β : Q ⟶ Q ⋙ S ⋙ L := Functor.whiskerRight i Q ≫
    Functor.whiskerLeft C η ≫ Functor.whiskerRight s.inv L
  let ff := Localization.fullyFaithfulWhiskeringLeft Q W D
  let z : 𝟭 D ⟶ S ⋙ L := ff.preimage β
  refine ⟨z, ?_⟩
  intro K
  have hz := congr_app (ff.map_preimage (X := 𝟭 D) (Y := S ⋙ L) β) K
  change z.app (Q.obj K) = β.app K at hz
  rw [hz]
  change (Q.map (i.app K) ≫ η.app (C.obj K) ≫ L.map (s.inv.app K)) ≫ _ = _
  rw [Category.assoc, Category.assoc, ← L.map_comp, s.inv_hom_id_app]
  exact (congrArg (fun v ↦ Q.map (i.app K) ≫ η.app (C.obj K) ≫ v)
      (L.map_id ((C ⋙ Q').obj K))).trans
    (congrArg (fun v ↦ Q.map (i.app K) ≫ v) (Category.comp_id (η.app (C.obj K))))

private theorem inverseComparisonSquare
    {C : Type*} [Category* C] {A B A' B' : C}
    (s : A ⟶ B) (t : A' ⟶ B') [IsIso s] [IsIso t]
    (a : A ⟶ A') (b : B ⟶ B') (h : s ≫ b = a ≫ t) :
    b ≫ inv t = inv s ≫ a :=
  (CommSq.horiz_inv (f := asIso s) (i := asIso t) ⟨h⟩).w.symm

section


open MonoidalCategory in
private def totalPullbackComparison
    {B : Type uB} [Category.{vB} B] [Abelian B] [MonoidalCategory B]
    {D : Type uD} [Category.{vD} D] [Abelian D] [MonoidalCategory D]
    [MonoidalPreadditive B] [MonoidalPreadditive D]
    [HasCoproducts.{0} B] [HasCoproducts.{0} D]
    (L : B ⥤ D) (V : D ⥤ B) [L.Additive] [V.Additive] (adj : L ⊣ V)
    (μ : ∀ M N : B, L.obj (M ⊗ N) ≅ L.obj M ⊗ L.obj N)
    (hμ : ∀ {M M' N N' : B} (f : M ⟶ M') (g : N ⟶ N'),
      L.map (f ⊗ₘ g) ≫ (μ M' N').hom = (μ M N).hom ≫ (L.map f ⊗ₘ L.map g)) :
    (Functor.postcompose₂.obj (L.mapHomologicalComplex (.up ℤ))).obj
        ((MonoidalCategory.curriedTensor B).map₂CochainComplex) ≅
      (((Functor.whiskeringLeft₂ (CochainComplex D ℤ)).obj
        (L.mapHomologicalComplex (.up ℤ))).obj
          (L.mapHomologicalComplex (.up ℤ))).obj
            ((MonoidalCategory.curriedTensor D).map₂CochainComplex) := by
  let LC := L.mapHomologicalComplex (.up ℤ)
  let tB := (MonoidalCategory.curriedTensor B).map₂CochainComplex
  let tD := (MonoidalCategory.curriedTensor D).map₂CochainComplex
  refine NatIso.ofComponents (fun K ↦ ?_) ?_
  · refine NatIso.ofComponents
      (fun F ↦ (@asIso _ _ _ _ (tensorPullbackTotal L μ hμ K F)
        (tensorPullbackTotal_isIso L μ hμ V adj K F)).symm) ?_
    intro F F' f
    have : IsIso (tensorPullbackTotal L μ hμ K F) :=
      tensorPullbackTotal_isIso L μ hμ V adj K F
    have : IsIso (tensorPullbackTotal L μ hμ K F') :=
      tensorPullbackTotal_isIso L μ hμ V adj K F' 
    change LC.map ((tB.obj K).map f) ≫ inv (tensorPullbackTotal L μ hμ K F') =
      inv (tensorPullbackTotal L μ hμ K F) ≫ (tD.obj (LC.obj K)).map (LC.map f)
    apply inverseComparisonSquare
    have h := CanonicalTensorPullbackOfUniverses.tensorPullbackTotal_naturality
      L μ hμ (𝟙 K) f
    simpa only [LC, tB, tD, Functor.map₂HomologicalComplex_obj_map,
      Functor.map₂HomologicalComplex_map_app, CategoryTheory.Functor.map_id] using h.symm
  · intro K K' f
    apply NatTrans.ext
    funext F
    have : IsIso (tensorPullbackTotal L μ hμ K F) :=
      tensorPullbackTotal_isIso L μ hμ V adj K F
    have : IsIso (tensorPullbackTotal L μ hμ K' F) :=
      tensorPullbackTotal_isIso L μ hμ V adj K' F
    change LC.map ((tB.map f).app F) ≫ inv (tensorPullbackTotal L μ hμ K' F) =
      inv (tensorPullbackTotal L μ hμ K F) ≫ (tD.map (LC.map f)).app (LC.obj F)
    apply inverseComparisonSquare
    have h := CanonicalTensorPullbackOfUniverses.tensorPullbackTotal_naturality
      L μ hμ f (𝟙 F)
    simpa only [LC, tB, tD, Functor.map₂HomologicalComplex_obj_map,
      Functor.map₂HomologicalComplex_map_app, CategoryTheory.Functor.map_id] using h.symm

end

open MonoidalCategory in
private theorem totalProjectionMap_app
    {B : Type uB} [Category.{vB} B] [Abelian B] [MonoidalCategory B]
    {D : Type uD} [Category.{vD} D] [Abelian D] [MonoidalCategory D]
    [MonoidalPreadditive B] [MonoidalPreadditive D]
    [HasCoproducts.{0} B] [HasCoproducts.{0} D]
    (L : B ⥤ D) (V : D ⥤ B) [L.Additive] [V.Additive] (adj : L ⊣ V)
    (μ : ∀ M N : B, L.obj (M ⊗ N) ≅ L.obj M ⊗ L.obj N)
    (hμ : ∀ {M M' N N' : B} (f : M ⟶ M') (g : N ⟶ N'),
      L.map (f ⊗ₘ g) ≫ (μ M' N').hom = (μ M N).hom ≫ (L.map f ⊗ₘ L.map g))
    (K : CochainComplex D ℤ) (F : CochainComplex B ℤ) :
    (((adj.mapHomologicalComplex (.up ℤ)).rightAdjointProjectionMap
        (totalPullbackComparison L V adj μ hμ).hom).app K).app F =
      tensorAdjunctionTotal L V adj μ hμ K F := by
  rfl


end ProjectionProof

section ProjectionCompatibility
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape
attribute [local irreducible] DerivedCategory.Q
attribute [local irreducible] HomologicalComplex₂.total HomologicalComplex.mapBifunctorMap

private theorem natTrans_ext_resolution
    {B : Type uB} [Category.{vB} B] {D : Type uD} [Category.{vD} D]
    (R : B ⥤ B) (i : 𝟭 B ⟶ R) (F G : B ⥤ D)
    (hi : ∀ K, IsIso (G.map (i.app K))) (a b : F ⟶ G)
    (h : ∀ K, a.app (R.obj K) = b.app (R.obj K)) : a = b := by
  ext K
  have := hi K
  apply (cancel_mono (G.map (i.app K))).1
  exact (a.naturality (i.app K)).symm.trans
    ((congrArg (fun v ↦ F.map (i.app K) ≫ v) (h K)).trans (b.naturality (i.app K)))

private theorem localizedNatTrans_ext_resolution
    {B : Type uB} [Category.{vB} B] {D : Type uD} [Category.{vD} D]
    {J : Type uI} [Category.{vI} J]
    (Q : B ⥤ D) (W : MorphismProperty B) [Q.IsLocalization W]
    (R : B ⥤ B) (i : 𝟭 B ⟶ R) (hi : ∀ K, IsIso (Q.map (i.app K)))
    (F G : D ⥤ J) (a b : F ⟶ G)
    (h : ∀ K, a.app (Q.obj (R.obj K)) = b.app (Q.obj (R.obj K))) : a = b := by
  apply (Localization.fullyFaithfulWhiskeringLeft Q W J).map_injective
  apply natTrans_ext_resolution R i (Q ⋙ F) (Q ⋙ G)
  · intro K
    have := hi K
    change IsIso (G.map (Q.map (i.app K)))
    infer_instance
  · exact h

private theorem transportAugmentation
    {B A TX TY D E DX DY : Type*}
    [Category* B] [Category* A] [Category* TX] [Category* TY]
    [Category* D] [Category* E] [Category* DX] [Category* DY]
    (QB : B ⥤ D) (W : MorphismProperty B) [QB.IsLocalization W]
    (QA : A ⥤ E) (QX : TX ⥤ DX) (QY : TY ⥤ DY)
    (V : B ⥤ A) (R : D ⥤ E) (δ : V ⋙ QA ⟶ QB ⋙ R)
    (CX : B ⥤ TX) (CY : A ⥤ TY) (FC : TX ⥤ TY)
    (S : E ⥤ DY) (T : D ⥤ DX) (Rt : DX ⥤ DY)
    (s : QA ⋙ S ≅ CY ⋙ QY) (t : QB ⋙ T ≅ CX ⋙ QX)
    (σ : V ⋙ CY ⟶ CX ⋙ FC) (u : R ⋙ S ⟶ T ⋙ Rt)
    (θ : FC ⋙ QY ⟶ QX ⋙ Rt)
    (PY : TY ⥤ A) (PX : TX ⥤ B) (LY : DY ⥤ E) (LX : DX ⥤ D)
    (ηY : PY ⋙ QA ⟶ QY ⋙ LY) (ηX : PX ⋙ QB ⟶ QX ⋙ LX)
    (o : PX ⋙ V ≅ FC ⋙ PY) (a : LX ⋙ R ≅ Rt ⋙ LY)
    (hnorm : ∀ I, δ.app (PX.obj I) ≫ R.map (ηX.app I) ≫ a.hom.app (QX.obj I) =
      QA.map (o.hom.app I) ≫ ηY.app (FC.obj I) ≫ LY.map (θ.app I))
    (iY : 𝟭 A ⟶ CY ⋙ PY) (iX : 𝟭 B ⟶ CX ⋙ PX)
    (zY : 𝟭 E ⟶ S ⋙ LY) (zX : 𝟭 D ⟶ T ⋙ LX)
    (hi : ∀ K, iY.app (V.obj K) ≫ PY.map (σ.app K) =
      V.map (iX.app K) ≫ o.hom.app (CX.obj K))
    (hzY : ∀ N, zY.app (QA.obj N) ≫ LY.map (s.hom.app N) =
      QA.map (iY.app N) ≫ ηY.app (CY.obj N))
    (hzX : ∀ K, zX.app (QB.obj K) ≫ LX.map (t.hom.app K) =
      QB.map (iX.app K) ≫ ηX.app (CX.obj K))
    (hu : ∀ K, S.map (δ.app K) ≫ u.app (QB.obj K) ≫ Rt.map (t.hom.app K) =
      s.hom.app (V.obj K) ≫ QY.map (σ.app K) ≫ θ.app (CX.obj K))
    (RI : B ⥤ B) (ι : 𝟭 B ⟶ RI) (hι : ∀ K, IsIso (QB.map (ι.app K)))
    (hδ : ∀ K, IsIso (δ.app (RI.obj K))) :
    ∀ M, zY.app (R.obj M) ≫ LY.map (u.app M) =
      R.map (zX.app M) ≫ a.hom.app (T.obj M) := by
  let α : R ⟶ T ⋙ Rt ⋙ LY :=
    Functor.whiskerLeft R zY ≫ Functor.whiskerRight u LY
  let β : R ⟶ T ⋙ Rt ⋙ LY :=
    Functor.whiskerRight zX R ≫ Functor.whiskerLeft T a.hom
  have h : α = β := by
    refine localizedNatTrans_ext_resolution QB W RI ι hι _ _ α β ?_
    intro K
    let I := RI.obj K
    have := hδ K
    have : IsIso (Rt.map (t.hom.app I)) := by infer_instance
    apply (cancel_epi (δ.app I)).1
    apply (cancel_mono (LY.map (Rt.map (t.hom.app I)))).1
    change (δ.app I ≫ (zY.app (R.obj (QB.obj I)) ≫ LY.map (u.app (QB.obj I)))) ≫ _ =
      (δ.app I ≫ (R.map (zX.app (QB.obj I)) ≫ a.hom.app (T.obj (QB.obj I)))) ≫ _
    have hz : δ.app I ≫ zY.app (R.obj (QB.obj I)) =
        zY.app (QA.obj (V.obj I)) ≫ LY.map (S.map (δ.app I)) := zY.naturality _
    have he : QA.map (PY.map (σ.app I)) ≫ ηY.app (FC.obj (CX.obj I)) =
        ηY.app (CY.obj (V.obj I)) ≫ LY.map (QY.map (σ.app I)) := ηY.naturality _
    have hd : QA.map (V.map (iX.app I)) ≫ δ.app (PX.obj (CX.obj I)) =
        δ.app I ≫ R.map (QB.map (iX.app I)) := δ.naturality _
    have ha : R.map (LX.map (t.hom.app I)) ≫ a.hom.app (QX.obj (CX.obj I)) =
        a.hom.app (T.obj (QB.obj I)) ≫ LY.map (Rt.map (t.hom.app I)) :=
      a.hom.naturality _
    calc
      _ = zY.app (QA.obj (V.obj I)) ≫ LY.map
          (S.map (δ.app I) ≫ u.app (QB.obj I) ≫ Rt.map (t.hom.app I)) := by
        simpa only [LY.map_comp, Category.assoc] using
          congrArg (fun v ↦ v ≫ LY.map (u.app (QB.obj I)) ≫
            LY.map (Rt.map (t.hom.app I))) hz
      _ = (zY.app (QA.obj (V.obj I)) ≫ LY.map (s.hom.app (V.obj I))) ≫
          LY.map (QY.map (σ.app I)) ≫ LY.map (θ.app (CX.obj I)) := by
        simpa only [LY.map_comp, Category.assoc] using congrArg
          (fun v ↦ zY.app (QA.obj (V.obj I)) ≫ LY.map v) (hu I)
      _ = QA.map (iY.app (V.obj I)) ≫ QA.map (PY.map (σ.app I)) ≫
          ηY.app (FC.obj (CX.obj I)) ≫ LY.map (θ.app (CX.obj I)) := by
        rw [hzY (V.obj I)]
        simpa only [Category.assoc] using congrArg
          (fun v ↦ QA.map (iY.app (V.obj I)) ≫ v ≫ LY.map (θ.app (CX.obj I))) he.symm
      _ = QA.map (V.map (iX.app I)) ≫ QA.map (o.hom.app (CX.obj I)) ≫
          ηY.app (FC.obj (CX.obj I)) ≫ LY.map (θ.app (CX.obj I)) := by
        simpa only [QA.map_comp, Category.assoc] using congrArg
          (fun v ↦ QA.map v ≫ ηY.app (FC.obj (CX.obj I)) ≫ LY.map (θ.app (CX.obj I)))
          (hi I)
      _ = QA.map (V.map (iX.app I)) ≫ δ.app (PX.obj (CX.obj I)) ≫
          R.map (ηX.app (CX.obj I)) ≫ a.hom.app (QX.obj (CX.obj I)) := by
        simpa only [Category.assoc] using congrArg
          (fun v ↦ QA.map (V.map (iX.app I)) ≫ v) (hnorm (CX.obj I)).symm
      _ = δ.app I ≫ R.map (QB.map (iX.app I) ≫ ηX.app (CX.obj I)) ≫
          a.hom.app (QX.obj (CX.obj I)) := by
        simpa only [R.map_comp, Category.assoc] using congrArg
          (fun v ↦ v ≫ R.map (ηX.app (CX.obj I)) ≫ a.hom.app (QX.obj (CX.obj I))) hd
      _ = δ.app I ≫ R.map (zX.app (QB.obj I) ≫ LX.map (t.hom.app I)) ≫
          a.hom.app (QX.obj (CX.obj I)) := by rw [hzX I]
      _ = _ := by
        simpa only [R.map_comp, Category.assoc] using congrArg
          (fun v ↦ δ.app I ≫ R.map (zX.app (QB.obj I)) ≫ v) ha
  intro M
  exact congr_app h M

private theorem evaluationRectangle
    {C : Type*} [Category* C]
    {U V W Z H J K U₁ W₁ V₁ V₂ V₃ V₄ L : C}
    (x : U ⟶ V) (q : V ⟶ W) (v : W ⟶ Z) (d : Z ⟶ H)
    (t : H ⟶ J) (e : J ⟶ K)
    (s : U ⟶ U₁) (a : U₁ ⟶ W) (b : Z ⟶ W₁) (c : W₁ ⟶ J)
    (sh : U₁ ⟶ V₁) (σ : V₁ ⟶ V₂) (θ : V₂ ⟶ W₁)
    (h : V₂ ⟶ V₃) (δ : V₃ ⟶ K) (cy : V₁ ⟶ V₄) (cs : V₄ ⟶ V₃)
    (m : U ⟶ V₄) (π : V ⟶ L) (tx : L ⟶ H) (n : L ⟶ K)
    [Epi x] [Mono (t ≫ e)]
    (hx : x ≫ q = s ≫ a) (hd : d ≫ t = b ≫ c)
    (hu : a ≫ v ≫ b = sh ≫ σ ≫ θ) (hθ : θ ≫ c ≫ e = h ≫ δ)
    (hσ : σ ≫ h = cy ≫ cs) (hm : s ≫ sh ≫ cy = m)
    (hn : tx ≫ t ≫ e = n) (hcan : x ≫ π ≫ n = m ≫ cs ≫ δ) :
    q ≫ v ≫ d = π ≫ tx := by
  apply (cancel_epi x).1
  apply (cancel_mono (t ≫ e)).1
  simp only [Category.assoc]
  calc
    _ = s ≫ a ≫ v ≫ b ≫ c ≫ e := by
      calc
        _ = (s ≫ a) ≫ v ≫ d ≫ t ≫ e := by
          simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ v ≫ d ≫ t ≫ e) hx
        _ = _ := by
          simp only [Category.assoc]
          rw [← Category.assoc d t e, hd]
          simp only [Category.assoc]
    _ = s ≫ sh ≫ σ ≫ θ ≫ c ≫ e := by
      simpa only [Category.assoc] using congrArg (fun f ↦ s ≫ f ≫ c ≫ e) hu
    _ = s ≫ sh ≫ σ ≫ h ≫ δ := by rw [hθ]
    _ = s ≫ sh ≫ cy ≫ cs ≫ δ := by
      simpa only [Category.assoc] using congrArg (fun f ↦ s ≫ sh ≫ f ≫ δ) hσ
    _ = m ≫ cs ≫ δ := by
      simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ cs ≫ δ) hm
    _ = x ≫ π ≫ n := hcan.symm
    _ = _ := by rw [hn]

private theorem mappedIdentityEquation
    {C D : Type*} [Category* C] [Category* D] (Q : C ⥤ D) (K : C)
    {U V : D} (x : U ⟶ V) (a : U ⟶ Q.obj K) (b : Q.obj K ⟶ V)
    (h : x = a ≫ b) : x = a ≫ Q.map (𝟙 K) ≫ b := by
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using h

private theorem identityMiddleEquation
    {C : Type*} [Category* C] {U V W : C}
    (a : U ⟶ V) (b : V ⟶ W) (c : U ⟶ W) (h : a ≫ b = c) :
    a ≫ 𝟙 V ≫ b = c := by
  simpa only [Category.id_comp, Category.comp_id] using h

private theorem transportProjectionEvaluation
    {B A D E TX TY DX DY : Type*}
    [Category* B] [Category* A] [Category* D] [Category* E]
    [Category* TX] [Category* TY] [Category* DX] [Category* DY]
    (QB : B ⥤ D) (W : MorphismProperty B) [QB.IsLocalization W]
    (QA : A ⥤ E) (QX : TX ⥤ DX) (QY : TY ⥤ DY)
    (V : B ⥤ A) (R : D ⥤ E) (δ : V ⋙ QA ⟶ QB ⋙ R)
    (CX : B ⥤ TX) (CY : A ⥤ TY) (FC : TX ⥤ TY)
    (S : E ⥤ DY) (T : D ⥤ DX) (Rt : DX ⥤ DY)
    (s : QA ⋙ S ≅ CY ⋙ QY) (t : QB ⋙ T ≅ CX ⋙ QX)
    (σ : V ⋙ CY ⟶ CX ⋙ FC) (u : R ⋙ S ⟶ T ⋙ Rt)
    (θ : FC ⋙ QY ⟶ QX ⋙ Rt)
    (hu : ∀ K, S.map (δ.app K) ≫ u.app (QB.obj K) ≫ Rt.map (t.hom.app K) =
      s.hom.app (V.obj K) ≫ QY.map (σ.app K) ≫ θ.app (CX.obj K))
    (ex : DX ⥤ D) (ey : DY ⥤ E) (exC : TX ⥤ B) (eyC : TY ⥤ A)
    (qev : ∀ J, eyC.obj (FC.obj J) ≅ V.obj (exC.obj J))
    (evX : QX ⋙ ex ≅ exC ⋙ QB) (evY : QY ⋙ ey ≅ eyC ⋙ QA)
    (ed : Rt ⋙ ey ≅ ex ⋙ R)
    (hed : ∀ J, ey.map (θ.app J) ≫ ed.hom.app (QX.obj J) ≫
        R.map (evX.hom.app J) = evY.hom.app (FC.obj J) ≫
          QA.map (qev J).hom ≫ δ.app (exC.obj J))
    (NX : B ⥤ B) (NY : A ⥤ A) (cx : CX ⋙ exC ≅ NX) (cy : CY ⋙ eyC ≅ NY)
    (τ : V ⋙ NY ⟶ NX ⋙ V)
    (hτ : ∀ K, eyC.map (σ.app K) ≫ (qev (CX.obj K)).hom ≫
      V.map (cx.hom.app K) =
      cy.hom.app (V.obj K) ≫ τ.app K)
    (PY : E ⥤ E) (PX : D ⥤ D) (a : PY ≅ S ⋙ ey) (b : PX ≅ T ⋙ ex)
    (m : ∀ K, PY.obj (QA.obj K) ⟶ QA.obj (NY.obj K))
    (n : ∀ K, PX.obj (QB.obj K) ⟶ QB.obj (NX.obj K))
    (hm : ∀ K, a.hom.app (QA.obj K) ≫ ey.map (s.hom.app K) ≫
      evY.hom.app (CY.obj K) ≫ QA.map (cy.hom.app K) = m K)
    (hn : ∀ K, b.hom.app (QB.obj K) ≫ ex.map (t.hom.app K) ≫
      evX.hom.app (CX.obj K) ≫ QB.map (cx.hom.app K) = n K)
    (π : R ⋙ PY ⟶ PX ⋙ R)
    (RI : B ⥤ B) (ι : 𝟭 B ⟶ RI) (hRI : ∀ K, IsIso (QB.map (ι.app K)))
    (hδ : ∀ K, IsIso (δ.app (RI.obj K)))
    (hcan : ∀ K, PY.map (δ.app (RI.obj K)) ≫ π.app (QB.obj (RI.obj K)) ≫
      R.map (n (RI.obj K)) = m (V.obj (RI.obj K)) ≫ QA.map (τ.app (RI.obj K)) ≫
        δ.app (NX.obj (RI.obj K))) :
    ∀ M, a.hom.app (R.obj M) ≫ ey.map (u.app M) ≫ ed.hom.app (T.obj M) =
      π.app M ≫ R.map (b.hom.app M) := by
  let α : R ⋙ PY ⟶ T ⋙ ex ⋙ R :=
    Functor.whiskerLeft R a.hom ≫ Functor.whiskerRight u ey ≫
      Functor.whiskerLeft T ed.hom
  let β : R ⋙ PY ⟶ T ⋙ ex ⋙ R := π ≫ Functor.whiskerRight b.hom R
  have hab : α = β := by
    refine localizedNatTrans_ext_resolution QB W RI ι hRI _ _ α β ?_
    intro K₀
    let K := RI.obj K₀
    let J := CX.obj K
    let v := u.app (QB.obj K)
    let x := PY.map (δ.app K)
    let q := a.hom.app (R.obj (QB.obj K))
    let vv := ey.map v
    let dd := ed.hom.app (T.obj (QB.obj K))
    let tt := R.map (ex.map (t.hom.app K))
    let ee := R.map (evX.hom.app J ≫ QB.map (cx.hom.app K))
    let ss := a.hom.app (QA.obj (V.obj K))
    let aa := ey.map (S.map (δ.app K))
    let bb := ey.map (Rt.map (t.hom.app K))
    let cc := ed.hom.app (QX.obj J)
    let sh := ey.map (s.hom.app (V.obj K))
    let σ' := ey.map (QY.map (σ.app K))
    let θ' := ey.map (θ.app J)
    let hh := evY.hom.app (FC.obj J) ≫
      QA.map ((qev J).hom ≫ V.map (cx.hom.app K))
    let δδ := δ.app (NX.obj K)
    let cyy := evY.hom.app (CY.obj (V.obj K)) ≫ QA.map (cy.hom.app (V.obj K))
    let ccs := QA.map (τ.app K)
    let mm := m (V.obj K)
    let pp := π.app (QB.obj K)
    let tx := R.map (b.hom.app (QB.obj K))
    let nn := R.map (n K)
    have : IsIso (δ.app K) := hδ K₀
    have : Epi x := by dsimp only [x]; infer_instance
    have : Mono (tt ≫ ee) := by dsimp only [tt, ee]; infer_instance
    have hx : x ≫ q = ss ≫ aa := a.hom.naturality (δ.app K)
    have hd : dd ≫ tt = bb ≫ cc := (ed.hom.naturality (t.hom.app K)).symm
    have huu : aa ≫ vv ≫ bb = sh ≫ σ' ≫ θ' := by
      simpa only [Functor.map_comp] using congrArg ey.map (hu K)
    have hθ : θ' ≫ cc ≫ ee = hh ≫ δδ := by
      have h := transportEvaluationSquare R θ' cc (evX.hom.app J)
        (QB.map (cx.hom.app K))
        (evY.hom.app (FC.obj J) ≫ QA.map (qev J).hom)
        (QA.map (V.map (cx.hom.app K))) _ δδ
        (by simpa only [θ', cc, J, Functor.comp_obj, Category.assoc] using hed J)
        (δ.naturality (cx.hom.app K)).symm
      simpa only [hh, QA.map_comp, Category.assoc] using h
    have hσ : σ' ≫ hh = cyy ≫ ccs := by
      exact transportNaturalitySquare QA σ' _ _ _ (cy.hom.app (V.obj K))
        ((qev J).hom ≫ V.map (cx.hom.app K)) _
        (evY.hom.naturality (σ.app K)) (hτ K)
    have hmm : ss ≫ sh ≫ cyy = mm := hm (V.obj K)
    have hnn : tx ≫ tt ≫ ee = nn := by
      simpa only [tx, tt, ee, nn, R.map_comp, Category.assoc] using congrArg R.map (hn K)
    exact evaluationRectangle x q vv dd tt ee ss aa bb cc sh σ' θ' hh δδ cyy ccs mm
      pp tx nn hx hd huu hθ hσ hmm hnn (hcan K₀)
  intro M
  exact congr_app hab M

private theorem evaluationNormalizedOfResolutions
    {B : Type uB} [Category.{vB} B] [Abelian B]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    {DB DD TB TD : Type*} [Category* DB] [Category* DD] [Category* TB] [Category* TD]
    (QY : CochainComplex B ℤ ⥤ DB) (QX : CochainComplex D ℤ ⥤ DD)
    (QTY : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ TB)
    (QTX : CochainComplex (ℕᵒᵖ ⥤ D) ℤ ⥤ TD)
    [QX.IsLocalization (HomologicalComplex.quasiIso D (.up ℤ))]
    (V : D ⥤ B) [V.Additive] (RF : DD ⥤ DB) (RT : TD ⥤ TB)
    (δ : V.mapHomologicalComplex (.up ℤ) ⋙ QY ⟶ QX ⋙ RF)
    (θ : (projectionPost V).mapHomologicalComplex (.up ℤ) ⋙ QTY ⟶ QTX ⋙ RT)
    (evY : TB ⥤ ℕᵒᵖ ⥤ DB) (evX : TD ⥤ ℕᵒᵖ ⥤ DD)
    (εY : QTY ⋙ evY ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ projectionPost QY)
    (εX : QTX ⋙ evX ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ projectionPost QX)
    (εV : RT ⋙ evY ≅ evX ⋙ projectionPost RF)
    (R : CochainComplex (ℕᵒᵖ ⥤ D) ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ D) ℤ)
    (i : 𝟭 (CochainComplex (ℕᵒᵖ ⥤ D) ℤ) ⟶ R)
    (hi : ∀ K, QuasiIso (i.app K))
    (hn : ∀ K n, (evY.map (θ.app (R.obj K))).app n ≫
      (εV.hom.app (QTX.obj (R.obj K))).app n ≫
      RF.map ((εX.hom.app (R.obj K)).app n) =
      (εY.hom.app (((projectionPost V).mapHomologicalComplex (.up ℤ)).obj (R.obj K))).app n ≫
        δ.app ((R.obj K).asFunctor.obj n))
    (I : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (n : ℕᵒᵖ) :
    (evY.map (θ.app I)).app n ≫
      (εV.hom.app (QTX.obj I)).app n ≫ RF.map ((εX.hom.app I).app n) =
      (εY.hom.app (((projectionPost V).mapHomologicalComplex (.up ℤ)).obj I)).app n ≫
        δ.app (I.asFunctor.obj n) := by
  let FC := (projectionPost (I := ℕᵒᵖ) V).mapHomologicalComplex (.up ℤ)
  let evX := HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    (CategoryTheory.evaluation ℕᵒᵖ (CochainComplex D ℤ)).obj n
  let ex := (CategoryTheory.evaluation ℕᵒᵖ DD).obj n
  let ey := (CategoryTheory.evaluation ℕᵒᵖ DB).obj n
  let α : FC ⋙ QTY ⋙ evY ⋙ ey ⟶
      evX ⋙ QX ⋙ RF :=
    Functor.whiskerRight θ (evY ⋙ ey) ≫
      Functor.whiskerLeft QTX (Functor.whiskerRight εV.hom ey) ≫
      Functor.whiskerRight (Functor.whiskerRight εX.hom ex) RF
  let β : FC ⋙ QTY ⋙ evY ⋙ ey ⟶
      evX ⋙ QX ⋙ RF :=
    Functor.whiskerLeft FC (Functor.whiskerRight εY.hom ey) ≫
      Functor.whiskerLeft evX δ
  have heq : α = β := by
    refine natTrans_ext_resolution R i _ _ ?_ α β ?_
    · intro K
      have hqi : QuasiIso (i.app K) := hi K
      have hq : QuasiIso (evX.map (i.app K)) :=
        ((HomologicalComplex.quasiIso_iff_evaluation _).1 hqi) n
      have : IsIso (QX.map (evX.map (i.app K))) :=
        Localization.inverts QX (HomologicalComplex.quasiIso D (.up ℤ)) _ hq
      change IsIso (RF.map (QX.map (evX.map (i.app K))))
      infer_instance
    · intro K
      exact hn K n
  exact congr_app heq I

private theorem towerEvaluationNormalized
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    [e.pushforward.Additive]
    [HasDerivedCategory.{w} X.projectionTowers]
    [HasDerivedCategory.{w} Y.projectionTowers]
    [HasCountableProducts X.mateDerived] [HasCountableProducts Y.mateDerived]
    (lx : StrictProjectionLimit X) (ly : StrictProjectionLimit Y)
    (d : StrictProjectionDirectImage e lx ly)
    (I : CochainComplex X.projectionTowers ℤ) (n : ℕᵒᵖ) :
    (ly.ev.map (d.towerEta.app I)).app n ≫
        (d.evaluation.hom.app (DerivedCategory.Q.obj I)).app n ≫
        e.right.map ((lx.evaluation.hom.app I).app n) =
      (ly.evaluation.hom.app
        ((e.projectionTowerPushforward.mapHomologicalComplex (.up ℤ)).obj I)).app n ≫
        d.eta.app (I.asFunctor.obj n) := by
  have : IsGrothendieckAbelian.{u} X.mateModules :=
    (grothendieckAbelian_and_functorial_kInjective_resolutions X.topology X.ring).1
  have : IsGrothendieckAbelian.{u} X.projectionTowers := by
    have := smallModuleDiagrams_isGrothendieckAbelian X.topology
      ((sheafCompose X.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj X.ring)
      (ULiftHom.{u} (ULift.{u} ℕᵒᵖ))
    exact IsGrothendieckAbelian.of_equivalence
      (ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ).congrLeft.symm
  let R := CochainComplex.kInjectiveResolutionFunctor.{u} X.projectionTowers
  let i := CochainComplex.toKInjectiveResolution.{u} X.projectionTowers
  exact evaluationNormalizedOfResolutions DerivedCategory.Q DerivedCategory.Q
    DerivedCategory.Q DerivedCategory.Q e.pushforward e.right d.Rt d.eta d.towerEta
    ly.ev lx.ev ly.evaluation lx.evaluation d.evaluation R i
    (fun K ↦ (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u}
      X.projectionTowers K).2)
    (fun K n ↦ d.evaluation_normalized (R.obj K)
      (CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u}
        X.projectionTowers K) n) I n

section ChainProjectionUnit

open MonoidalCategory

variable {B : Type uB} [Category.{vB} B] [Abelian B] [MonoidalCategory B]
  {D : Type uD} [Category.{vD} D] [Abelian D] [MonoidalCategory D]
  [MonoidalPreadditive B] [MonoidalPreadditive D]
  [HasCoproducts.{0} B] [HasCoproducts.{0} D]
  (L : B ⥤ D) (V : D ⥤ B) [L.Additive] [V.Additive] (adj : L ⊣ V)
  (μ : ∀ M N : B, L.obj (M ⊗ N) ≅ L.obj M ⊗ L.obj N)
  (hμ : ∀ {M M' N N' : B} (f : M ⟶ M') (g : N ⟶ N'),
    L.map (f ⊗ₘ g) ≫ (μ M' N').hom = (μ M N).hom ≫ (L.map f ⊗ₘ L.map g))
  (j : L.obj (𝟙_ B) ≅ 𝟙_ D)
  (hj : ∀ M : B, (μ M (𝟙_ B)).hom ≫ (𝟙 (L.obj M) ⊗ₘ j.hom) ≫
    (ρ_ (L.obj M)).hom = L.map (ρ_ M).hom)

omit [Abelian B] [Abelian D] [MonoidalPreadditive B] [MonoidalPreadditive D]
  [HasCoproducts B] [HasCoproducts D] [L.Additive] [V.Additive] in
include hj in
private theorem ordinaryProjectionUnit (M : D) :
    (ρ_ (V.obj M)).inv ≫ tensorAdjunctionMate L V adj μ M (𝟙_ B) =
      V.map ((ρ_ M).inv ≫ (𝟙 M ⊗ₘ j.inv)) := by
  have ht : tensorAdjunctionMate L V adj μ M (𝟙_ B) ≫
      V.map ((𝟙 M ⊗ₘ j.hom) ≫ (ρ_ M).hom) = (ρ_ (V.obj M)).hom := by
    unfold tensorAdjunctionMate
    rw [← adj.homEquiv_naturality_right]
    apply (adj.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    rw [← hj]
    simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Category.comp_id,
      Category.id_comp]
    have hcomm : adj.counit.app M ⊗ₘ j.hom =
        (𝟙 (L.obj (V.obj M)) ⊗ₘ j.hom) ≫
          (adj.counit.app M ⊗ₘ 𝟙 (𝟙_ D)) := by
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    rw [hcomm]
    simp only [Category.assoc, tensorHom_id]
    rw [rightUnitor_naturality]
  apply (cancel_mono (V.map ((𝟙 M ⊗ₘ j.hom) ≫ (ρ_ M).hom))).1
  rw [Category.assoc, ht, Iso.inv_hom_id, ← V.map_comp]
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id,
    Category.id_comp, Category.comp_id, tensorHom_id, id_whiskerRight,
    CategoryTheory.Functor.map_id]

private theorem unitorInvComponent (K : CochainComplex B ℤ) (r : ℤ) :
    (HomologicalComplex.rightUnitor K).inv.f r =
      (ρ_ (K.X r)).inv ≫ CochainComplex.ιMapBifunctor K
        ((CochainComplex.singleFunctor B 0).obj (𝟙_ B))
        (curriedTensor B) r 0 r (add_zero r) := by
  change (HomologicalComplex.rightUnitor' K).inv r = _
  rw [HomologicalComplex.rightUnitor'_inv]
  simp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    eqToIso_refl, Iso.refl_inv]
  change (ρ_ (K.X r)).inv ≫ (K.X r ◁ 𝟙 (𝟙_ B)) ≫ _ = _
  rw [whiskerLeft_id, Category.id_comp]
  rfl

omit [MonoidalCategory D] [MonoidalPreadditive B] [MonoidalPreadditive D]
  [HasCoproducts B] [HasCoproducts D] in
private theorem singlePullbackInvComponent :
    (((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).app (𝟙_ B)).inv).f 0 =
      𝟙 (L.obj (𝟙_ B)) := by
  change ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).inv.app
    (𝟙_ B)).f 0 = _
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
  change L.map (𝟙 (𝟙_ B)) = 𝟙 (L.obj (𝟙_ B))
  exact L.map_id _

include hμ hj in
private theorem totalProjectionUnit (K : CochainComplex D ℤ) :
    (HomologicalComplex.rightUnitor
      ((V.mapHomologicalComplex (.up ℤ)).obj K)).inv ≫
        tensorAdjunctionTotal L V adj μ hμ K
          ((CochainComplex.singleFunctor B 0).obj (𝟙_ B)) =
      (V.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.rightUnitor K).inv ≫
          (((curriedTensor D).map₂CochainComplex.obj K).map
            (((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).app (𝟙_ B) ≪≫
              (CochainComplex.singleFunctor D 0).mapIso j).inv))) := by
  apply HomologicalComplex.Hom.ext
  funext r
  simp only [HomologicalComplex.comp_f, unitorInvComponent]
  rw [Category.assoc, CategoryTheory.tensorAdjunctionTotal_summand]
  erw [← Category.assoc, ordinaryProjectionUnit L V adj μ j hj]
  change V.map _ ≫ V.map _ = V.map _
  rw [← V.map_comp]
  apply congrArg V.map
  rw [HomologicalComplex.comp_f, unitorInvComponent]
  simp only [Functor.map₂HomologicalComplex_obj_map, Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [Iso.trans_inv, Functor.mapIso_inv, HomologicalComplex.comp_f,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    NatTrans.id_app, HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, CategoryTheory.Functor.map_id,
    Category.id_comp, HomologicalComplex.id_f,
    curriedTensor_obj_map, Category.assoc]
  erw [singlePullbackInvComponent L]
  change (ρ_ (K.X r)).inv ≫ (𝟙 (K.X r) ⊗ₘ j.inv) ≫ _ =
    (ρ_ (K.X r)).inv ≫ (K.X r ◁ (j.inv ≫ 𝟙 _ ≫ 𝟙 _)) ≫ _
  simp only [Category.comp_id, id_tensorHom]
  rfl

include hμ hj in
private theorem existsTotalProjectionMate :
    ∃ σ : V.mapHomologicalComplex (.up ℤ) ⋙ (curriedTensor B).map₂CochainComplex ⟶
        (Functor.postcompose₂.obj (V.mapHomologicalComplex (.up ℤ))).obj
          ((((Functor.whiskeringLeft₂ (CochainComplex D ℤ)).obj
            (𝟭 (CochainComplex D ℤ))).obj
              (L.mapHomologicalComplex (.up ℤ))).obj (curriedTensor D).map₂CochainComplex),
      (∀ (K : CochainComplex D ℤ) (F : CochainComplex B ℤ),
        (σ.app K).app F = tensorAdjunctionTotal L V adj μ hμ K F) ∧
      ∀ K : CochainComplex D ℤ,
        (HomologicalComplex.rightUnitor
          ((V.mapHomologicalComplex (.up ℤ)).obj K)).inv ≫
            (σ.app K).app ((CochainComplex.singleFunctor B 0).obj (𝟙_ B)) =
          (V.mapHomologicalComplex (.up ℤ)).map
            ((HomologicalComplex.rightUnitor K).inv ≫
              (((curriedTensor D).map₂CochainComplex.obj K).map
                (((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).app (𝟙_ B) ≪≫
                  (CochainComplex.singleFunctor D 0).mapIso j).inv))) := by
  let σ := (adj.mapHomologicalComplex (.up ℤ)).rightAdjointProjectionMap
    (totalPullbackComparison L V adj μ hμ).hom
  refine ⟨σ, ?_, ?_⟩
  · intro K F
    exact totalProjectionMap_app L V adj μ hμ K F
  · intro K
    dsimp only [σ]
    rw [totalProjectionMap_app]
    exact totalProjectionUnit L V adj μ hμ j hj K

end ChainProjectionUnit

private theorem augmentProjectionUnit
    {C D : Type*} [Category* C] [Category* D] (V : D ⥤ C) (L : C ⥤ D)
    (TY : C ⥤ C) (TX : D ⥤ D) (τ : TY ⟶ L ⋙ TX ⋙ V)
    {U : C} {W N : D} (y : V.obj N ⟶ TY.obj U) (x : N ⟶ TX.obj W)
    (j : L.obj U ≅ W)
    (hu : y ≫ τ.app U = V.map (x ≫ TX.map j.inv)) {F : C} (z : U ⟶ F) :
    y ≫ TY.map z ≫ τ.app F = V.map (x ≫ TX.map (j.inv ≫ L.map z)) := by
  calc
    _ = (y ≫ τ.app U) ≫ V.map (TX.map (L.map z)) := by
      rw [Category.assoc, τ.naturality z]
      rfl
    _ = V.map (x ≫ TX.map j.inv) ≫ V.map (TX.map (L.map z)) :=
      congrArg (fun f ↦ f ≫ V.map (TX.map (L.map z))) hu
    _ = _ := by rw [← V.map_comp, TX.map_comp, Category.assoc]

private theorem limitPushforwardSquare
    {B A I : Type*} [Category* B] [Category* A] [Category* I]
    [Preadditive B] [Preadditive A] [HasLimitsOfShape I B] [HasLimitsOfShape I A]
    (V : B ⥤ A) [V.Additive]
    (o : (lim : (I ⥤ B) ⥤ B) ⋙ V ≅ projectionPost V ⋙ (lim : (I ⥤ A) ⥤ A))
    (ho : ∀ H, o.hom.app H = limit.post H V)
    (K : CochainComplex B ℤ) (TX : CochainComplex (I ⥤ B) ℤ)
    (TY : CochainComplex (I ⥤ A) ℤ)
    (σ : TY ⟶ ((projectionPost V).mapHomologicalComplex (.up ℤ)).obj TX)
    (iY : (V.mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((lim : (I ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj TY)
    (iX : K ⟶ ((lim : (I ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)).obj TX)
    (h : ∀ r n, (iY.f r ≫ limit.π (TY.X r) n) ≫ (σ.f r).app n =
      V.map (iX.f r ≫ limit.π (TX.X r) n)) :
    iY ≫ ((lim : (I ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).map σ =
      (V.mapHomologicalComplex (.up ℤ)).map iX ≫
        (NatTrans.mapHomologicalComplex o.hom (.up ℤ)).app TX := by
  apply HomologicalComplex.Hom.ext
  funext r
  apply limit.hom_ext
  intro n
  change (iY.f r ≫ limMap (σ.f r)) ≫ limit.π _ n =
    (V.map (iX.f r) ≫ o.hom.app (TX.X r)) ≫ limit.π _ n
  simp only [Category.assoc, limMap_π, ho]
  erw [limit.post_π]
  simpa only [Category.assoc, V.map_comp] using h r n


private theorem homotopyPushforwardData
    {B : Type uB} [Category.{vB} B] [Abelian B]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} D]
    (V : B ⥤ D) [V.Additive] (RF : DerivedCategory B ⥤ DerivedCategory D)
    (δ : V.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hδ : RF.IsRightDerivedFunctor δ (HomologicalComplex.quasiIso B (.up ℤ))) :
    ∃ η : V.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF,
      (∀ G : DerivedCategory B ⥤ DerivedCategory D,
        Function.Bijective (fun b : RF ⟶ G ↦ η ≫ Functor.whiskerLeft DerivedCategory.Qh b)) ∧
      (∀ K, derivedPushforwardComplexComparison V RF η K = δ.app K) := by
  let q := HomotopyCategory.quotient B (.up ℤ)
  let F := V.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let eF : q ⋙ F ≅ V.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight (V.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft (V.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso D)
  let eQ := DerivedCategory.quotientCompQhIso B
  let ff := Functor.FullyFaithful.ofFullyFaithful
    ((Functor.whiskeringLeft _ _ (DerivedCategory D)).obj q)
  let η : F ⟶ DerivedCategory.Qh ⋙ RF :=
    ff.preimage (eF.hom ≫ δ ≫ (Functor.isoWhiskerRight eQ RF).inv)
  have hη : Functor.whiskerLeft q η =
      eF.hom ≫ δ ≫ (Functor.isoWhiskerRight eQ RF).inv := ff.map_preimage _
  have hδeq : eF.inv ≫ Functor.whiskerLeft q η ≫
      (Functor.isoWhiskerRight eQ RF).hom = δ := by
    rw [hη]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨η, ?_, ?_⟩
  · intro G
    let E : (F ⟶ DerivedCategory.Qh ⋙ G) ≃
        (V.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ G) :=
      ff.homEquiv.trans (Iso.homCongr eF (Functor.isoWhiskerRight eQ G))
    have htransport (b : RF ⟶ G) :
        E (η ≫ Functor.whiskerLeft DerivedCategory.Qh b) =
          δ ≫ Functor.whiskerLeft DerivedCategory.Q b := by
      have hn : Functor.whiskerLeft (q ⋙ DerivedCategory.Qh) b ≫
          (Functor.isoWhiskerRight eQ G).hom =
        (Functor.isoWhiskerRight eQ RF).hom ≫ Functor.whiskerLeft DerivedCategory.Q b := by
        ext K
        exact (b.naturality (eQ.hom.app K)).symm
      change eF.inv ≫ (Functor.whiskerLeft q η ≫
          Functor.whiskerLeft (q ⋙ DerivedCategory.Qh) b) ≫
          (Functor.isoWhiskerRight eQ G).hom = _
      simp only [Category.assoc]
      rw [hn]
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ Functor.whiskerLeft DerivedCategory.Q b) hδeq
    have : RF.IsLeftKanExtension δ :=
      (Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ _).1 hδ
    have hb : Function.Bijective
        (fun b : RF ⟶ G ↦ E (η ≫ Functor.whiskerLeft DerivedCategory.Qh b)) := by
      simp only [htransport]
      exact (RF.homEquivOfIsLeftKanExtension δ G).bijective
    constructor
    · intro b b' h
      exact hb.1 (congrArg E h)
    · intro τ
      obtain ⟨b, h⟩ := hb.2 (E τ)
      exact ⟨b, E.injective h⟩
  · intro K
    have h := congr_app hδeq K
    change ((DerivedCategory.quotientCompQhIso D).inv.app
        ((V.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map ((V.mapHomotopyCategoryFactors (.up ℤ)).inv.app K)) ≫
        η.app (q.obj K) ≫ RF.map ((DerivedCategory.quotientCompQhIso B).hom.app K) =
          δ.app K at h
    simpa only [derivedPushforwardComplexComparison, q, Category.assoc] using h

private theorem inverseTransport
    {C : Type*} [Category* C] {A B X Y : C} (i : A ≅ X) (j : B ≅ Y)
    (f : X ⟶ Y) [IsIso f] (p : A ⟶ B)
    (h : p ≫ j.hom ≫ inv f ≫ i.inv = 𝟙 A) :
    p = i.hom ≫ f ≫ j.inv := by
  apply (cancel_mono (j.hom ≫ inv f ≫ i.inv)).1
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, IsIso.hom_inv_id_assoc,
    Iso.hom_inv_id]

private theorem inverseRectangle
    {C : Type*} [Category* C] {A B X Y M N : C}
    (i : A ≅ X) (j : B ≅ Y) (f : X ⟶ Y) [IsIso f] (p : A ⟶ B)
    (x : M ⟶ A) (c : M ⟶ X) (b : B ⟶ N) (y : Y ⟶ N)
    (hp : p ≫ j.hom ≫ inv f ≫ i.inv = 𝟙 A)
    (hi : x ≫ i.hom = c) (hj : j.inv ≫ b = y) :
    x ≫ p ≫ b = c ≫ f ≫ y := by
  rw [inverseTransport i j f p hp]
  simp only [Category.assoc]
  rw [hj, ← Category.assoc x i.hom, hi]

private theorem mappedInverseFirstCancel
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (T : C × D ⥤ E) {X Y : C} (i : X ≅ Y) (Z : D) {W : E}
    (c : T.obj (X, Z) ≅ W) :
    T.map (Prod.mkHom i.hom (𝟙 Z)) ≫
      (T.mapIso (Iso.prod i.symm (Iso.refl Z)) ≪≫ c).hom = c.hom := by
  change (T.mapIso (Iso.prod i (Iso.refl Z))).hom ≫
    ((T.mapIso (Iso.prod i (Iso.refl Z))).symm ≪≫ c).hom = _
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

private theorem compositeInverseCancel
    {C : Type*} [Category* C] {A B D : C} (j : A ≅ B) (k : D ≅ B) :
    (j ≪≫ k.symm).inv ≫ j.hom = k.hom := by
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem inverseMateNormalization
    {C D : Type*} [Category* C] [Category* D]
    (T : C × C ⥤ C) (R : D ⥤ C) {N F M W : C} {E H J : D}
    (δK : N ≅ R.obj E) (c : T.obj (N, F) ≅ M)
    (b : H ≅ J) (δJ : W ≅ R.obj J) (f : M ⟶ W) [IsIso f]
    (π : T.obj (R.obj E, F) ⟶ R.obj H)
    (h : π ≫ (R.mapIso b ≪≫ δJ.symm).hom ≫ inv f ≫
      (T.mapIso (Iso.prod δK.symm (Iso.refl F)) ≪≫ c).inv = 𝟙 _) :
    T.map (Prod.mkHom δK.hom (𝟙 F)) ≫ π ≫ R.map b.hom = c.hom ≫ f ≫ δJ.hom := by
  exact inverseRectangle (T.mapIso (Iso.prod δK.symm (Iso.refl F)) ≪≫ c)
    (R.mapIso b ≪≫ δJ.symm) f π _ c.hom (R.map b.hom) δJ.hom h
    (mappedInverseFirstCancel T δK F c) (compositeInverseCancel (R.mapIso b) δJ)

private theorem inverseMateNormalizationRefl
    {B C D : Type*} [Category* B] [Category* C] [Category* D]
    (Q : B ⥤ C) (T : C × C ⥤ C) (R : D ⥤ C)
    {N F : C} {Z W : B} {E H J : D}
    (δK : N ≅ R.obj E) (c : T.obj (N, F) ≅ Q.obj Z)
    (b : H ≅ J) (δJ : Q.obj W ≅ R.obj J) (f : Z ⟶ W) [IsIso f]
    (π : T.obj (R.obj E, F) ⟶ R.obj H)
    (h : π ≫ (R.mapIso b ≪≫ δJ.symm).hom ≫ Q.map (inv f) ≫
      (T.mapIso (Iso.prod (R.mapIso (Iso.refl E) ≪≫ δK.symm)
        (Iso.refl F)) ≪≫ c).inv = 𝟙 _) :
    T.map (Prod.mkHom δK.hom (𝟙 F)) ≫ π ≫ R.map b.hom =
      c.hom ≫ Q.map f ≫ δJ.hom := by
  apply inverseMateNormalization T R δK c b δJ (Q.map f) π
  simpa only [Functor.mapIso_refl, Iso.refl_trans, Functor.map_inv] using h

private theorem transportMateComparison
    {B C D : Type*} [Category* B] [Category* C] [Category* D]
    (Q : B ⥤ C) (T : C × C ⥤ C) (R : D ⥤ C)
    {N F : C} {Z W : B} {E H J : D}
    (δ δ' : N ⟶ R.obj E) (θ θ' : Q.obj W ⟶ R.obj J)
    (c : T.obj (N, F) ⟶ Q.obj Z) (b : H ⟶ J)
    (π : T.obj (R.obj E, F) ⟶ R.obj H) (f g : Z ⟶ W)
    (hδ : δ' = δ) (hθ : θ' = θ) (hf : f = g)
    (h : T.map (Prod.mkHom δ' (𝟙 F)) ≫ π ≫ R.map b = c ≫ Q.map g ≫ θ') :
    T.map (Prod.mkHom δ (𝟙 F)) ≫ π ≫ R.map b = c ≫ Q.map f ≫ θ := by
  cases hδ
  cases hθ
  cases hf
  exact h

set_option backward.isDefEq.respectTransparency.types false in
private theorem canonicalProjectionChainSquare
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X) [e.pushforward.Additive]
    (δ : e.pushforward.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ e.right)
    (K : CochainComplex X.mateModules ℤ) (hK : K.IsKInjective)
    (F : CochainComplex Y.mateModules ℤ)
    (P : StrictPerfectCoefficientPackage
      ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring) F)
    (f : (Y.projectionTotal.obj
        ((e.pushforward.mapHomologicalComplex (.up ℤ)).obj K)).obj F ⟶
      (e.pushforward.mapHomologicalComplex (.up ℤ)).obj
        ((X.projectionTotal.obj K).obj
          ((e.pullback.mapHomologicalComplex (.up ℤ)).obj F)))
    (hδ : e.right.IsRightDerivedFunctor δ
      (HomologicalComplex.quasiIso X.mateModules (.up ℤ)))
    (computeR : ∀ K : CochainComplex X.mateModules ℤ,
      K.IsKInjective → IsIso (δ.app K))
    (canonicalAdj : e.ProjectionCounitNormalized δ)
    (hb : ∃ lo hi : ℤ, ∀ r : ℤ, r < lo ∨ hi < r → IsZero (F.X r))
    (hF : Y.mateFlat F)
    (hLF : X.mateFlat ((e.pullback.mapHomologicalComplex (.up ℤ)).obj F))
    (hf : f =
      (let := monoidalCategory Y.ring
       let := monoidalCategory X.ring
       let := ringedTensorPreadditive Y.ring
       let := ringedTensorPreadditive X.ring
       tensorAdjunctionTotal e.pullback e.pushforward e.moduleAdjunction
         e.ordinaryTensor.mu e.ordinaryTensor.naturality K F)) :
    Y.tensor.map (Prod.mkHom (δ.app K) (𝟙 (DerivedCategory.Q.obj F))) ≫
      derivedProjectionFormulaMate e.left e.right e.derivedAdjunction Y.tensor X.tensor
        (e.tensorComparison a b) (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj F) ≫
      e.right.map (X.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj K))
          (derivedPullbackComplexComparison e.pullback e.left e.epsilon F)) ≫
        (mixedTensorRepresentative X.ring X.mateFlat (fun _ ↦ Iff.rfl)
          X.tensor b.representative K
          ((e.pullback.mapHomologicalComplex (.up ℤ)).obj F) hLF).hom) =
      (mixedTensorRepresentative Y.ring Y.mateFlat (fun _ ↦ Iff.rfl)
        Y.tensor a.representative ((e.pushforward.mapHomologicalComplex (.up ℤ)).obj K)
        F hF).hom ≫
        DerivedCategory.Q.map f ≫
        δ.app ((X.projectionTotal.obj K).obj
          ((e.pullback.mapHomologicalComplex (.up ℤ)).obj F)) := by
  -- Cache the direct additive parent of the existing sheaf abelian instance.
  let : Abelian Y.mateModules :=
    { (inferInstance : Abelian Y.mateModules) with
      toPreadditive := (inferInstance : Preadditive Y.mateModules) }
  let : Abelian X.mateModules :=
    { (inferInstance : Abelian X.mateModules) with
      toPreadditive := (inferInstance : Preadditive X.mateModules) }
  let := monoidalCategory Y.ring
  let := monoidalCategory X.ring
  let := ringedTensorPreadditive Y.ring
  let := ringedTensorPreadditive X.ring
  let : ∀ K L : CochainComplex Y.mateModules ℤ,
      HomologicalComplex.HasMapBifunctor K L Y.mateTensor (.up ℤ) :=
    @tensorComplexHasTotal Y.mateModules _ _ (monoidalCategory Y.ring)
      (ringedTensorPreadditive Y.ring) _
  let : ∀ K L : CochainComplex X.mateModules ℤ,
      HomologicalComplex.HasMapBifunctor K L X.mateTensor (.up ℤ) :=
    @tensorComplexHasTotal X.mateModules _ _ (monoidalCategory X.ring)
      (ringedTensorPreadditive X.ring) _
  let hηData := homotopyPushforwardData e.pushforward e.right δ hδ
  let η := hηData.choose
  have hη := hηData.choose_spec.1
  have heq := hηData.choose_spec.2
  have computeR' (I : CochainComplex X.mateModules ℤ) (hi : I.IsKInjective) :
      IsIso (derivedPushforwardComplexComparison e.pushforward e.right η I) := by
    rw [heq I]
    exact computeR I hi
  have computeL (G : CochainComplex Y.mateModules ℤ) (hg : G.IsAcyclicTensorKFlat)
      (ht : ∀ n : ℤ, (G.X n).IsFlat) := pullbackFlatComputes e G ⟨hg, ht⟩
  have ca (I : CochainComplex X.mateModules ℤ) (hi : I.IsKInjective) :
      e.left.map (derivedPushforwardComplexComparison e.pushforward e.right η I) ≫
        e.derivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
      derivedPullbackComplexComparison e.pullback e.left e.epsilon
        ((e.pushforward.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((e.moduleAdjunction.mapHomologicalComplex (.up ℤ)).counit.app I) := by
    exact (congrArg (fun v ↦ e.left.map v ≫
      e.derivedAdjunction.counit.app (DerivedCategory.Q.obj I)) (heq I)).trans
        (canonicalAdj I hi)
  have hl := ringedProjectionFormula_totalization_left e.inverse e.direct e.adjunction
    e.algebraic e.ringMap e.pullback e.object_eq e.map_eq e.left e.epsilon e.isLeftDerived
    Y.mateFlat X.mateFlat (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl)
    Y.tensor X.tensor a.representative b.representative e.ordinaryTensor
    e.pushforward e.moduleAdjunction e.right η hη computeR' computeL
    e.derivedAdjunction ca (DerivedCategory.Q.obj K) K hK (Iso.refl _) F P hb
  let j := e.projectionUnit
  have hj := Classical.choose_spec (canonicalRingedTensorComparison_unit
    Y.ring X.ring e.inverseRing e.inverse e.algebraic e.ringMap e.pullback
    e.object_eq e.map_eq e.ordinaryTensor).exists
  let J := CochainComplex.mapBifunctor K
    ((e.pullback.mapHomologicalComplex (.up ℤ)).obj F)
    (MonoidalCategory.curriedTensor X.mateModules)
  have hJ : CochainComplex.IsKInjective J :=
    tensorAdjunctionTotal_target_isKInjective e.pullback j K hK F
      hb P.N P.i P.p P.splitting
  have := computeR K hK
  have := computeR J hJ
  have := computeR' K hK
  have := computeR' J hJ
  have := computeL F hF.1 hF.2
  let c := mixedTensorRepresentative Y.ring Y.mateFlat (fun _ ↦ Iff.rfl)
    Y.tensor a.representative ((e.pushforward.mapHomologicalComplex (.up ℤ)).obj K) F hF
  let b₀ := X.tensor.mapIso (Iso.prod (Iso.refl (DerivedCategory.Q.obj K))
      (asIso (derivedPullbackComplexComparison e.pullback e.left e.epsilon F))) ≪≫
    mixedTensorRepresentative X.ring X.mateFlat (fun _ ↦ Iff.rfl)
      X.tensor b.representative K ((e.pullback.mapHomologicalComplex (.up ℤ)).obj F) hLF
  let i := Y.tensor.mapIso (Iso.prod
    (e.right.mapIso (Iso.refl (DerivedCategory.Q.obj K)) ≪≫
      (asIso (derivedPushforwardComplexComparison e.pushforward e.right η K)).symm)
    (Iso.refl (DerivedCategory.Q.obj F))) ≪≫ c
  let j₀ := e.right.mapIso b₀ ≪≫
    (asIso (derivedPushforwardComplexComparison e.pushforward e.right η J)).symm
  let g := tensorAdjunctionTotal e.pullback e.pushforward e.moduleAdjunction
    e.ordinaryTensor.mu e.ordinaryTensor.naturality K F
  have hg : IsIso g := tensorAdjunctionTotal_isIso e.pullback e.pushforward e.moduleAdjunction
    e.ordinaryTensor.mu e.ordinaryTensor.naturality j hj K F hb P.N P.i P.p P.splitting
  have hp : derivedProjectionFormulaMate e.left e.right e.derivedAdjunction Y.tensor X.tensor
      (e.tensorComparison a b) (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj F) ≫
        j₀.hom ≫ DerivedCategory.Q.map (inv g) ≫ i.inv = 𝟙 _ := by
    exact hl
  have hs := inverseMateNormalizationRefl DerivedCategory.Q Y.tensor e.right
    (asIso (derivedPushforwardComplexComparison e.pushforward e.right η K)) c b₀
    (asIso (derivedPushforwardComplexComparison e.pushforward e.right η J))
    g _ hp
  exact transportMateComparison DerivedCategory.Q Y.tensor e.right
    (δ.app K) (derivedPushforwardComplexComparison e.pushforward e.right η K)
    (δ.app J) (derivedPushforwardComplexComparison e.pushforward e.right η J)
    c.hom b₀.hom _ f g (heq K) (heq J) hf hs

end ProjectionCompatibility

private def tensorFirst {C : Type*} [Category* C]
    (T : C × C ⥤ C) (F : C) : C ⥤ C where
  obj E := T.obj (E, F)
  map f := T.map (Prod.mkHom f (𝟙 F))
  map_id E := by rw [← prod_id]; exact T.map_id (E, F)
  map_comp f g := by
    simpa only [prod_comp, Category.comp_id] using
      T.map_comp (Prod.mkHom f (𝟙 F)) (Prod.mkHom g (𝟙 F))

private def projectionFirstTransformation
    {C D : Type*} [Category* C] [Category* D]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    (TY : C × C ⥤ C) (TX : D × D ⥤ D)
    (α : TY ⋙ L ≅ L.prod L ⋙ TX) (F : C) :
    R ⋙ tensorFirst TY F ⟶ tensorFirst TX (L.obj F) ⋙ R where
  app E := derivedProjectionFormulaMate L R adj TY TX α E F
  naturality _ _ f :=
    congr_app ((adj.rightAdjointProjectionMap
      (T_C := Functor.curry.obj TX) (T_D := Functor.curry.obj TY)
      (Functor.curry.map α.hom ≫ (Functor.curryObjProdComp L L TX).hom)).naturality f) F

section ProjectionConstruction
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] DerivedCategory.Q
attribute [local irreducible] HomologicalComplex₂.total HomologicalComplex.mapBifunctorMap
attribute [local irreducible] CochainComplex.kInjectiveResolutionFunctor
  CochainComplex.toKInjectiveResolution
attribute [local irreducible] monoidalCategory mixedTensorRepresentative
  RingedTensorCorner.projectionRightUnitor RingedTensorEdge.tensorComparison


private theorem constructTowerSide
    (B : Type uB) [Category.{vB} B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]
    {DB DT : Type*} [Category* DB] [Category* DT]
    (Q : CochainComplex B ℤ ⥤ DB) (QT : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ DT)
    [Q.IsLocalization (HomologicalComplex.quasiIso B (.up ℤ))]
    [QT.IsLocalization (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ))]
    {J : Type uI} [Category.{vI} J]
    (ev : DT ⥤ ℕᵒᵖ ⥤ DB)
    (evIso : QT ⋙ ev ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ projectionPost Q)
    (T : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (P : J ⥤ ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (C : CochainComplex B ℤ ⥤ J ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (S : DB ⥤ J ⥤ DT)
    (s : Q ⋙ S ≅ C ⋙ projectionPost QT)
    (c : C ⋙ projectionPost
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅ rawTensorDiagrams T P)
    (U : CochainComplex B ℤ) (ρ : ∀ N, (T.obj N).obj U ≅ N)
    (hρ : ∀ {N N' : CochainComplex B ℤ} (f : N ⟶ N'),
      f ≫ (ρ N').inv = (ρ N).inv ≫ (T.map f).app U)
    (aug : ∀ p, (Functor.const ℕᵒᵖ).obj U ⟶ P.obj p)
    (L : DT ⥤ DB)
    (η : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ) ⋙ Q ⟶
      QT ⋙ L)
    (F : J → ℕᵒᵖ → DB ⥤ DB)
    (mixed : ∀ p n K, (F p n).obj (Q.obj K) ≅
      Q.obj ((T.obj K).obj ((P.obj p).obj n)))
    (norm : ∀ p n, ∃ m : Q ⋙ F p n ≅
        T.flip.obj ((P.obj p).obj n) ⋙ Q,
      ∀ K, m.hom.app K = (mixed p n K).hom) :
    ∃ (e : ∀ p n, F p n ≅ S.flip.obj p ⋙ ev ⋙
          (CategoryTheory.evaluation ℕᵒᵖ (DB)).obj n)
      (i : ∀ p, 𝟭 (CochainComplex B ℤ) ⟶ C.flip.obj p ⋙
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ))
      (z : ∀ p, 𝟭 (DB) ⟶ S.flip.obj p ⋙ L),
      (∀ p n K, (e p n).hom.app (Q.obj K) ≫
        (ev.map ((s.hom.app K).app p)).app n ≫
        (evIso.hom.app ((C.obj K).obj p)).app n ≫
        Q.map (((c.hom.app K).app p).app n) = (mixed p n K).hom) ∧
      (∀ p N n r, ((i p).app N).f r ≫ limit.π (((C.obj N).obj p).X r) n ≫
        (((c.hom.app N).app p).app n).f r =
          ((ρ N).inv ≫ (T.obj N).map ((aug p).app n)).f r) ∧
      (∀ p K, (z p).app (Q.obj K) ≫ L.map ((s.hom.app K).app p) =
        Q.map ((i p).app K) ≫ η.app ((C.obj K).obj p)) := by
  obtain ⟨e, he⟩ := chooseFamilies (fun p n ↦
    diagramTensorEvaluation B Q QT ev evIso T P C S s c p n (F p n) (mixed p n) (norm p n))
  obtain ⟨i, hi⟩ := chooseFamily (fun p ↦
    diagramCoaugmentation B T U ρ hρ P C c p (aug p))
  obtain ⟨z, hz⟩ := chooseFamily (fun p ↦
    descendCoaugmentation Q (HomologicalComplex.quasiIso B (.up ℤ))
      QT (C.flip.obj p) (S.flip.obj p)
      ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)) L η
      (coefficientIso Q QT S C s p) (i p))
  exact ⟨e, i, z, he, hi, hz⟩



private theorem constructTensorTowerMorphism
    (B : Type uB) [Category.{vB} B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]
    (D : Type uD) [Category.{vD} D] [Abelian D] [HasLimitsOfShape ℕᵒᵖ D]
    {DB DD TB TD : Type*} [Category* DB] [Category* DD] [Category* TB] [Category* TD]
    [HasCountableProducts DB] [HasShift DB ℤ] [Preadditive DB]
    (QY : CochainComplex B ℤ ⥤ DB) (QX : CochainComplex D ℤ ⥤ DD)
    (QTY : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ TB)
    (QTX : CochainComplex (ℕᵒᵖ ⥤ D) ℤ ⥤ TD)
    [QY.IsLocalization (HomologicalComplex.quasiIso B (.up ℤ))]
    [QX.IsLocalization (HomologicalComplex.quasiIso D (.up ℤ))]
    [QTY.IsLocalization (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ))]
    [QTX.IsLocalization (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ D) (.up ℤ))]
    {J : Type uI} [Category.{vI} J]
    (V : D ⥤ B) [V.Additive]
    (LC : CochainComplex B ℤ ⥤ CochainComplex D ℤ)
    (R : DD ⥤ DB)
    (δ : V.mapHomologicalComplex (.up ℤ) ⋙ QY ⟶ QX ⋙ R)
    (TY : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (TX : CochainComplex D ℤ ⥤ CochainComplex D ℤ ⥤ CochainComplex D ℤ)
    (P : J ⥤ ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (σ : V.mapHomologicalComplex (.up ℤ) ⋙ TY ⟶
      (Functor.postcompose₂.obj (V.mapHomologicalComplex (.up ℤ))).obj
        ((((Functor.whiskeringLeft₂ (CochainComplex D ℤ)).obj
          (𝟭 (CochainComplex D ℤ))).obj LC).obj TX))
    (Rt : TD ⥤ TB)
    (θ : (projectionPost V).mapHomologicalComplex (.up ℤ) ⋙ QTY ⟶
      QTX ⋙ Rt)
    (evY : TB ⥤ ℕᵒᵖ ⥤ DB)
    (evX : TD ⥤ ℕᵒᵖ ⥤ DD)
    (εY : QTY ⋙ evY ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ projectionPost QY)
    (εX : QTX ⋙ evX ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ projectionPost QX)
    (εV : Rt ⋙ evY ≅ evX ⋙ projectionPost R)
    (UY : CochainComplex B ℤ) (UX : CochainComplex D ℤ)
    (ρY : ∀ N, (TY.obj N).obj UY ≅ N) (ρX : ∀ K, (TX.obj K).obj UX ≅ K)
    (j : LC.obj UY ≅ UX)
    (augY : ∀ p, (Functor.const ℕᵒᵖ).obj UY ⟶ P.obj p)
    (LY : TB ⥤ DB)
    (LX : TD ⥤ DD)
    (ηY : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ) ⋙ QY ⟶
      QTY ⋙ LY)
    (ηX : (lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ) ⋙ QX ⟶
      QTX ⋙ LX)
    (ordinary : (lim : (ℕᵒᵖ ⥤ D) ⥤ D) ⋙ V ≅
      projectionPost V ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B))
    (a : LX ⋙ R ≅ Rt ⋙ LY)
    (FY : J → ℕᵒᵖ → DB ⥤ DB)
    (FX₀ FX : J → ℕᵒᵖ → DD ⥤ DD)
    (κ : ∀ p n, FX p n ≅ FX₀ p n)
    (mY : ∀ p n N, (FY p n).obj (QY.obj N) ≅
      QY.obj ((TY.obj N).obj ((P.obj p).obj n)))
    (mX : ∀ p n K, (FX₀ p n).obj (QX.obj K) ≅
      QX.obj ((TX.obj K).obj (LC.obj ((P.obj p).obj n))))
    (π : ∀ p n, R ⋙ FY p n ⟶ FX p n ⋙ R)
    (RI : CochainComplex D ℤ ⥤ CochainComplex D ℤ)
    (ι : 𝟭 (CochainComplex D ℤ) ⟶ RI)
    (H : Prop)
    (pY : ∀ Z, LY.obj Z ⟶ ∏ᶜ fun n : ℕ ↦ (evY.obj Z).obj (op n))
    (dY : ∀ Z, (∏ᶜ fun n : ℕ ↦ (evY.obj Z).obj (op n)) ⟶ (LY.obj Z)⟦(1 : ℤ)⟧)
    (hY : ∀ {N N' : CochainComplex B ℤ} (f : N ⟶ N'), QuasiIso f →
      ∀ p n, QuasiIso ((TY.map f).app ((P.obj p).obj n)))
    (hX : ∀ {K K' : CochainComplex D ℤ} (f : K ⟶ K'), QuasiIso f →
      ∀ p n, QuasiIso ((TX.map f).app (LC.obj ((P.obj p).obj n))))
    (hv : ∀ I n, (evY.map (θ.app I)).app n ≫
      (εV.hom.app (QTX.obj I)).app n ≫ R.map ((εX.hom.app I).app n) =
      (εY.hom.app (((projectionPost V).mapHomologicalComplex (.up ℤ)).obj I)).app n ≫
        δ.app (I.asFunctor.obj n))
    (hρY : ∀ {N N' : CochainComplex B ℤ} (f : N ⟶ N'),
      f ≫ (ρY N').inv = (ρY N).inv ≫ (TY.map f).app UY)
    (hρX : ∀ {K K' : CochainComplex D ℤ} (f : K ⟶ K'),
      f ≫ (ρX K').inv = (ρX K).inv ≫ (TX.map f).app UX)
    (hunit : ∀ K, (ρY ((V.mapHomologicalComplex (.up ℤ)).obj K)).inv ≫
      (σ.app K).app UY = (V.mapHomologicalComplex (.up ℤ)).map
        ((ρX K).inv ≫ (TX.obj K).map j.inv))
    (hordinary : ∀ H, ordinary.hom.app H = limit.post H V)
    (ha : ∀ I, δ.app (((lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ)).obj I) ≫
      R.map (ηX.app I) ≫ a.hom.app (QTX.obj I) =
      QY.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app I) ≫
      ηY.app (((projectionPost V).mapHomologicalComplex (.up ℤ)).obj I) ≫ LY.map (θ.app I))
    (hmY : ∀ p n, ∃ m : QY ⋙ FY p n ≅
        TY.flip.obj ((P.obj p).obj n) ⋙ QY,
      ∀ N, m.hom.app N = (mY p n N).hom)
    (hmX : ∀ p n, ∃ m : QX ⋙ FX₀ p n ≅
        TX.flip.obj (LC.obj ((P.obj p).obj n)) ⋙ QX,
      ∀ K, m.hom.app K = (mX p n K).hom)
    (hι : ∀ K, IsIso (QX.map (ι.app K)))
    (hδ : ∀ K, IsIso (δ.app (RI.obj K)))
    (hcan : ∀ p n K, (FY p n).map (δ.app (RI.obj K)) ≫
      (π p n).app (QX.obj (RI.obj K)) ≫
        R.map ((κ p n).hom.app (QX.obj (RI.obj K)) ≫ (mX p n (RI.obj K)).hom) =
      (mY p n ((V.mapHomologicalComplex (.up ℤ)).obj (RI.obj K))).hom ≫
        QY.map ((σ.app (RI.obj K)).app ((P.obj p).obj n)) ≫
          δ.app ((TX.obj (RI.obj K)).obj (LC.obj ((P.obj p).obj n))))
    (hH : H)
    (hpY : ∀ {Z W} (v : Z ⟶ W), LY.map v ≫ pY W =
      pY Z ≫ Limits.Pi.map (fun n : ℕ ↦ (evY.map v).app (op n)))
    (hdY : ∀ {Z W} (v : Z ⟶ W),
      Limits.Pi.map (fun n : ℕ ↦ (evY.map v).app (op n)) ≫ dY W =
        dY Z ≫ (LY.map v)⟦(1 : ℤ)⟧') :
    ∃ (CY : CochainComplex B ℤ ⥤ J ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
      (CX : CochainComplex D ℤ ⥤ J ⥤ CochainComplex (ℕᵒᵖ ⥤ D) ℤ)
      (cy : CY ⋙ projectionPost
        HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅ rawTensorDiagrams TY P)
      (cx : CX ⋙ projectionPost HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
        rawTensorDiagrams TX (P ⋙ projectionPost LC))
      (S : DB ⥤ J ⥤ TB)
      (T : DD ⥤ J ⥤ TD)
      (s : QY ⋙ S ≅ CY ⋙ projectionPost QTY)
      (t : QX ⋙ T ≅ CX ⋙ projectionPost QTX)
      (_hFlat : H)
      (sEv : ∀ E p n, (FY p n).obj E ≅ (evY.obj ((S.obj E).obj p)).obj n)
      (tEv : ∀ E p n, (FX p n).obj E ≅ (evX.obj ((T.obj E).obj p)).obj n)
      (u : R ⋙ S ⟶ T ⋙ projectionPost Rt)
      (zY : ∀ p, 𝟭 (DB) ⟶ S.flip.obj p ⋙ LY)
      (zX : ∀ p, 𝟭 (DD) ⟶ T.flip.obj p ⋙ LX),
      (∀ N p n, (sEv (QY.obj N) p n).hom ≫
        (evY.map ((s.hom.app N).app p)).app n ≫
        (εY.hom.app ((CY.obj N).obj p)).app n ≫
        QY.map (((cy.hom.app N).app p).app n) = (mY p n N).hom) ∧
      (∀ K p n, (tEv (QX.obj K) p n).hom ≫
        (evX.map ((t.hom.app K).app p)).app n ≫
        (εX.hom.app ((CX.obj K).obj p)).app n ≫
        QX.map (((cx.hom.app K).app p).app n) =
          (κ p n).hom.app (QX.obj K) ≫ (mX p n K).hom) ∧
      (∀ p n {M M'} (g : M ⟶ M'), (FY p n).map g ≫ (sEv M' p n).hom =
        (sEv M p n).hom ≫ (evY.map ((S.map g).app p)).app n) ∧
      (∀ p n {E E'} (g : E ⟶ E'), (FX p n).map g ≫ (tEv E' p n).hom =
        (tEv E p n).hom ≫ (evX.map ((T.map g).app p)).app n) ∧
      (∀ E p n, (sEv (R.obj E) p n).hom ≫
        (evY.map ((u.app E).app p)).app n ≫ (εV.hom.app ((T.obj E).obj p)).app n =
          (π p n).app E ≫ R.map (tEv E p n).hom) ∧
      (∀ N p, ∃ i : N ⟶
          ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)).obj ((CY.obj N).obj p),
        (∀ n r, i.f r ≫ limit.π (((CY.obj N).obj p).X r) n ≫
          (((cy.hom.app N).app p).app n).f r =
            ((ρY N).inv ≫ (TY.obj N).map ((augY p).app n)).f r) ∧
        (zY p).app (QY.obj N) ≫ LY.map ((s.hom.app N).app p) =
          QY.map i ≫ ηY.app ((CY.obj N).obj p)) ∧
      (∀ K p, ∃ (z : (Functor.const ℕᵒᵖ).obj UX ⟶ (P ⋙ projectionPost LC).obj p)
          (i : K ⟶ ((lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ)).obj
            ((CX.obj K).obj p)),
        (∀ n, z.app n = j.inv ≫ LC.map ((augY p).app n)) ∧
        (∀ n r, i.f r ≫ limit.π (((CX.obj K).obj p).X r) n ≫
          (((cx.hom.app K).app p).app n).f r =
            ((ρX K).inv ≫ (TX.obj K).map (z.app n)).f r) ∧
        (zX p).app (QX.obj K) ≫ LX.map ((t.hom.app K).app p) =
          QX.map i ≫ ηX.app ((CX.obj K).obj p)) ∧
      (∀ E p, (zY p).app (R.obj E) ≫ LY.map ((u.app E).app p) =
        R.map ((zX p).app E) ≫ a.hom.app ((T.obj E).obj p)) ∧
      (∀ E p, LY.map ((u.app E).app p) ≫ pY (Rt.obj ((T.obj E).obj p)) =
        pY ((S.obj (R.obj E)).obj p) ≫
          Limits.Pi.map (fun n : ℕ ↦ (evY.map ((u.app E).app p)).app (op n))) ∧
      (∀ E p, Limits.Pi.map (fun n : ℕ ↦ (evY.map ((u.app E).app p)).app (op n)) ≫
          towerTransitionEndomorphism (fun n : ℕ ↦
            (evY.obj (Rt.obj ((T.obj E).obj p))).map (homOfLE (Nat.le_succ n)).op) =
        towerTransitionEndomorphism (fun n : ℕ ↦
          (evY.obj ((S.obj (R.obj E)).obj p)).map (homOfLE (Nat.le_succ n)).op) ≫
          Limits.Pi.map (fun n : ℕ ↦ (evY.map ((u.app E).app p)).app (op n))) ∧
      (∀ E p, Limits.Pi.map (fun n : ℕ ↦ (evY.map ((u.app E).app p)).app (op n)) ≫
          dY (Rt.obj ((T.obj E).obj p)) =
        dY ((S.obj (R.obj E)).obj p) ≫ (LY.map ((u.app E).app p))⟦(1 : ℤ)⟧') := by
  classical
  let VC := V.mapHomologicalComplex (.up ℤ)
  let FC := (projectionPost (I := ℕᵒᵖ) V).mapHomologicalComplex (.up ℤ)
  let DY := rawTensorDiagrams TY P
  let DX := rawTensorDiagrams TX (P ⋙ projectionPost LC)
  obtain ⟨CY, ⟨cy⟩⟩ := existsComplexDiagrams DY
  obtain ⟨CX, ⟨cx⟩⟩ := existsComplexDiagrams DX
  obtain ⟨S, ⟨s⟩⟩ := descendComplexDiagrams B QY QTY CY DY cy hY
  obtain ⟨T, ⟨t⟩⟩ := descendComplexDiagrams D QX QTX CX DX cx hX
  obtain ⟨τ, hτ⟩ := liftDiagramMorphism V VC CY CX DY DX cy cx
    (tensorDiagramMate VC LC TY TX P σ)
  obtain ⟨u, hu⟩ := liftNormalizedProjection QX
    (HomologicalComplex.quasiIso D (.up ℤ)) QY
    (projectionPost QTX) (projectionPost QTY)
    VC R δ CX CY (projectionPost FC) S T (projectionPost Rt) s t τ
    (postDiagramTransformation FC QTY QTX Rt θ) RI ι hι hδ
  let augX p := mapAugmentation LC j (augY p)
  obtain ⟨eY, iY, zY, heY, hiY, hzY⟩ :=
    constructTowerSide B QY QTY evY εY TY P CY S s cy UY ρY hρY augY LY ηY FY mY hmY
  obtain ⟨eX₀, iX, zX, heX₀, hiX, hzX⟩ :=
    constructTowerSide D QX QTX evX εX TX (P ⋙ projectionPost LC) CX T t cx UX ρX hρX
      augX LX ηX FX₀ mX hmX
  let eX p n := κ p n ≪≫ eX₀ p n
  have heX p n K : (eX p n).hom.app (QX.obj K) ≫
      (evX.map ((t.hom.app K).app p)).app n ≫
      (εX.hom.app ((CX.obj K).obj p)).app n ≫
      QX.map (((cx.hom.app K).app p).app n) =
        (κ p n).hom.app (QX.obj K) ≫ (mX p n K).hom := by
    exact prependNormalization _ _ _ _ _ _ (heX₀ p n K) (by rfl)
  have hu' K p := congr_app (hu K) p
  have heval (E : DD) (p : J) (n : ℕᵒᵖ) :
      (eY p n).hom.app (R.obj E) ≫ (evY.map ((u.app E).app p)).app n ≫
        (εV.hom.app ((T.obj E).obj p)).app n =
      (π p n).app E ≫ R.map ((eX p n).hom.app E) := by
    let exC := HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (CategoryTheory.evaluation ℕᵒᵖ (CochainComplex D ℤ)).obj n
    let eyC := HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (CategoryTheory.evaluation ℕᵒᵖ (CochainComplex B ℤ)).obj n
    exact transportProjectionEvaluation QX
      (HomologicalComplex.quasiIso D (.up ℤ)) QY
      QTX QTY VC R δ
      (CX.flip.obj p) (CY.flip.obj p) FC (S.flip.obj p) (T.flip.obj p) Rt
      (coefficientIso QY QTY S CY s p)
      (coefficientIso QX QTX T CX t p)
      (Functor.whiskerRight τ ((CategoryTheory.evaluation J
        (CochainComplex (ℕᵒᵖ ⥤ B) ℤ)).obj p))
      (Functor.whiskerRight u ((CategoryTheory.evaluation J _).obj p)) θ (fun K ↦ hu' K p)
      (evX ⋙ (CategoryTheory.evaluation ℕᵒᵖ (DD)).obj n)
      (evY ⋙ (CategoryTheory.evaluation ℕᵒᵖ (DB)).obj n)
      exC eyC (fun _ ↦ Iso.refl _)
      (levelComparisonIso QX QTX evX
        HomologicalComplex.complexOfFunctorsToFunctorToComplex εX n)
      (levelComparisonIso QY QTY evY
        HomologicalComplex.complexOfFunctorsToFunctorToComplex εY n)
      (levelComparisonIso R Rt evY evX εV n)
      (fun I ↦ mappedIdentityEquation QY
        (VC.obj (I.asFunctor.obj n)) _ _ _ (hv I n))
      (TX.flip.obj (LC.obj ((P.obj p).obj n))) (TY.flip.obj ((P.obj p).obj n))
      (comparisonLevelIso TX (P ⋙ projectionPost LC) CX cx p n)
      (comparisonLevelIso TY P CY cy p n)
      (((flipFunctor _ _ _).map σ).app ((P.obj p).obj n))
      (fun K ↦ identityMiddleEquation _ _ _ (hτ K p n))
      (FY p n) (FX p n) (eY p n) (eX p n) (fun N ↦ (mY p n N).hom)
      (fun K ↦ (κ p n).hom.app (QX.obj K) ≫ (mX p n K).hom)
      (heY p n) (heX p n) (π p n) RI ι hι hδ (hcan p n) E
  have haugX (p : J) (n : ℕᵒᵖ) :
      (augX p).app n = j.inv ≫ LC.map ((augY p).app n) := rfl
  have hchain (K : CochainComplex D ℤ) (p : J) :
      (iY p).app (VC.obj K) ≫
        ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)).map ((τ.app K).app p) =
      VC.map ((iX p).app K) ≫
        (NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app ((CX.obj K).obj p) := by
    apply limitPushforwardSquare V ordinary hordinary K
      _ _ ((τ.app K).app p) ((iY p).app (VC.obj K)) ((iX p).app K)
    intro r n
    let cY := (((cy.hom.app (VC.obj K)).app p).app n).f r
    let cX := (((cx.hom.app K).app p).app n).f r
    have hY : (((iY p).app (VC.obj K)).f r ≫
        limit.π (((CY.obj (VC.obj K)).obj p).X r) n) ≫ cY =
        ((ρY (VC.obj K)).inv ≫ (TY.obj (VC.obj K)).map ((augY p).app n)).f r := by
      simpa only [cY, Category.assoc] using hiY p (VC.obj K) n r
    have hX : (((iX p).app K).f r ≫ limit.π (((CX.obj K).obj p).X r) n) ≫ cX =
        ((ρX K).inv ≫ (TX.obj K).map ((augX p).app n)).f r := by
      simpa only [cX, Category.assoc] using hiX p K n r
    have hc := HomologicalComplex.congr_hom
      (augmentProjectionUnit VC LC (TY.obj (VC.obj K)) (TX.obj K) (σ.app K)
        (ρY (VC.obj K)).inv (ρX K).inv j (hunit K) ((augY p).app n)) r
    rw [← haugX p n] at hc
    have ht := HomologicalComplex.congr_hom (hτ K p n) r
    apply transportChainSquare V _ cY _ cX _ _ _ _ hY hX ht
    simpa only [DX, rawTensorDiagrams, tensorDiagramMate, HomologicalComplex.comp_f, VC,
      Functor.mapHomologicalComplex_map_f,
      Functor.map_comp, Category.assoc] using hc
  have haug (E : DD) (p : J) :
      (zY p).app (R.obj E) ≫ LY.map ((u.app E).app p) =
        R.map ((zX p).app E) ≫ a.hom.app ((T.obj E).obj p) := by
    exact transportAugmentation QX
      (HomologicalComplex.quasiIso D (.up ℤ))
      QY QTX QTY VC R δ
      (CX.flip.obj p) (CY.flip.obj p) FC (S.flip.obj p) (T.flip.obj p) Rt
      (coefficientIso QY QTY S CY s p)
      (coefficientIso QX QTX T CX t p)
      (Functor.whiskerRight τ ((CategoryTheory.evaluation J
        (CochainComplex (ℕᵒᵖ ⥤ B) ℤ)).obj p))
      (Functor.whiskerRight u ((CategoryTheory.evaluation J _).obj p)) θ
      ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ))
      ((lim : (ℕᵒᵖ ⥤ D) ⥤ D).mapHomologicalComplex (.up ℤ))
      LY LX ηY ηX (NatIso.mapHomologicalComplex ordinary (.up ℤ)) a ha
      (iY p) (iX p) (zY p) (zX p) (fun K ↦ hchain K p) (hzY p) (hzX p)
      (fun K ↦ hu' K p) RI ι hι hδ E
  let sEv E p n := (eY p n).app E
  let tEv E p n := (eX p n).app E
  refine ⟨CY, CX, cy, cx, S, T, s, t, hH, sEv, tEv, u, zY, zX,
    (fun N p n ↦ heY p n N), (fun K p n ↦ heX p n K), ?_, ?_, heval,
    ?_, ?_, haug, ?_, ?_, ?_⟩
  · intro p n M M' g
    exact (eY p n).hom.naturality g
  · intro p n E E' g
    exact (eX p n).hom.naturality g
  · intro N p
    exact ⟨(iY p).app N, hiY p N, hzY p N⟩
  · intro K p
    exact ⟨augX p, (iX p).app K, fun _ ↦ rfl, hiX p K, hzX p K⟩
  · intro E p
    exact hpY ((u.app E).app p)
  · intro E p
    apply towerTransitionEndomorphism_natural_backward
    intro n
    exact ((evY.map ((u.app E).app p)).naturality (homOfLE (Nat.le_succ n)).op).symm
  · intro E p
    exact hdY ((u.app E).app p)

private theorem nativeProjectionMate
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    [e.pushforward.Additive] :
      ∃ σ : e.pushforward.mapHomologicalComplex (.up ℤ) ⋙ Y.projectionTotal ⟶
      (Functor.postcompose₂.obj (e.pushforward.mapHomologicalComplex (.up ℤ))).obj
        ((((Functor.whiskeringLeft₂ (CochainComplex X.mateModules ℤ)).obj
          (𝟭 (CochainComplex X.mateModules ℤ))).obj
            (e.pullback.mapHomologicalComplex (.up ℤ))).obj X.projectionTotal),
        (∀ (K : CochainComplex X.mateModules ℤ) (F : CochainComplex Y.mateModules ℤ),
          (σ.app K).app F =
                (let := monoidalCategory Y.ring
                 let := monoidalCategory X.ring
                 let := ringedTensorPreadditive Y.ring
                 let := ringedTensorPreadditive X.ring
                 tensorAdjunctionTotal e.pullback e.pushforward e.moduleAdjunction
                   e.ordinaryTensor.mu e.ordinaryTensor.naturality K F)) ∧
        ∀ K : CochainComplex X.mateModules ℤ,
          (Y.projectionRightUnitor
                  ((e.pushforward.mapHomologicalComplex (.up ℤ)).obj K)).inv ≫
                (σ.app K).app Y.mateUnitComplex =
                (e.pushforward.mapHomologicalComplex (.up ℤ)).map
                  ((X.projectionRightUnitor K).inv ≫ (X.projectionTotal.obj K).map
                    e.projectionUnitComplex.inv) := by
  classical
  -- Cache the direct additive parent of the existing sheaf abelian instance.
  let : Abelian Y.mateModules :=
    { (inferInstance : Abelian Y.mateModules) with
      toPreadditive := (inferInstance : Preadditive Y.mateModules) }
  let : Abelian X.mateModules :=
    { (inferInstance : Abelian X.mateModules) with
      toPreadditive := (inferInstance : Preadditive X.mateModules) }
  let := monoidalCategory Y.ring
  let := monoidalCategory X.ring
  let := ringedTensorPreadditive Y.ring
  let := ringedTensorPreadditive X.ring
  let : ∀ K L : CochainComplex Y.mateModules ℤ,
      HomologicalComplex.HasMapBifunctor K L Y.mateTensor (.up ℤ) :=
    @tensorComplexHasTotal Y.mateModules _ _ (monoidalCategory Y.ring)
      (ringedTensorPreadditive Y.ring) _
  let : ∀ K L : CochainComplex X.mateModules ℤ,
      HomologicalComplex.HasMapBifunctor K L X.mateTensor (.up ℤ) :=
    @tensorComplexHasTotal X.mateModules _ _ (monoidalCategory X.ring)
      (ringedTensorPreadditive X.ring) _
  with_unfolding_all
    exact existsTotalProjectionMate e.pullback e.pushforward
      e.moduleAdjunction e.ordinaryTensor.mu e.ordinaryTensor.naturality e.projectionUnit
      (Classical.choose_spec (canonicalRingedTensorComparison_unit Y.ring X.ring e.inverseRing
        e.inverse e.algebraic e.ringMap e.pullback e.object_eq e.map_eq e.ordinaryTensor).exists)

private theorem buildTowerProjection
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X)
    [e.pushforward.Additive]
    [HasDerivedCategory.{w} X.projectionTowers]
    [HasDerivedCategory.{w} Y.projectionTowers]
    [HasCountableProducts X.mateDerived] [HasCountableProducts Y.mateDerived]
    (lx : StrictProjectionLimit X) (ly : StrictProjectionLimit Y)
    (d : StrictProjectionDirectImage e lx ly) :
    towerProjectionResult e a b lx ly d := by
  change let Result : Prop := _; Result
  intro Result
  classical
  -- Cache the direct additive parent of the existing sheaf abelian instance.
  let : Abelian Y.mateModules :=
    { (inferInstance : Abelian Y.mateModules) with
      toPreadditive := (inferInstance : Preadditive Y.mateModules) }
  let : Abelian X.mateModules :=
    { (inferInstance : Abelian X.mateModules) with
      toPreadditive := (inferInstance : Preadditive X.mateModules) }
  let hσData := nativeProjectionMate e
  let σ := hσData.choose
  have hσ := hσData.choose_spec.1
  have hσunit := hσData.choose_spec.2
  let LC : CochainComplex Y.mateModules ℤ ⥤ CochainComplex X.mateModules ℤ :=
    e.pullback.mapHomologicalComplex (.up ℤ)
  let VC : CochainComplex X.mateModules ℤ ⥤ CochainComplex Y.mateModules ℤ :=
    e.pushforward.mapHomologicalComplex (.up ℤ)
  let hRIData :=
    (grothendieckAbelian_and_functorial_kInjective_resolutions X.topology X.ring).2.2
  let RI := hRIData.choose
  let ι := hRIData.choose_spec.choose
  have hRI := hRIData.choose_spec.choose_spec
  have hf (P : Y.projectionCoefficients) (n : ℕᵒᵖ) :
      Y.mateFlat (P.obj.right.obj n) ∧
        X.mateFlat ((e.projectionCoefficientDiagram.obj P).obj n) :=
    ⟨coefficientFlat Y P n, pullbackPreservesFlat e _ (coefficientFlat Y P n)⟩
  let FY (P : Y.projectionCoefficients) (n : ℕᵒᵖ) : Y.mateDerived ⥤ Y.mateDerived :=
    tensorFirst Y.tensor (DerivedCategory.Q.obj (P.obj.right.obj n))
  let FX (P : Y.projectionCoefficients) (n : ℕᵒᵖ) : X.mateDerived ⥤ X.mateDerived :=
    tensorFirst X.tensor (e.left.obj (DerivedCategory.Q.obj (P.obj.right.obj n)))
  let π (P : Y.projectionCoefficients) (n : ℕᵒᵖ) : e.right ⋙ FY P n ⟶ FX P n ⋙ e.right :=
    projectionFirstTransformation e.left e.right e.derivedAdjunction Y.tensor X.tensor
      (e.tensorComparison a b) (DerivedCategory.Q.obj (P.obj.right.obj n))
  let m (P : Y.projectionCoefficients) (n : ℕᵒᵖ) (N : CochainComplex Y.mateModules ℤ) :=
    (mixedTensorRepresentative Y.ring Y.mateFlat (fun _ ↦ Iff.rfl)
      Y.tensor a.representative N (P.obj.right.obj n) (hf P n).1).hom
  let nn (P : Y.projectionCoefficients) (n : ℕᵒᵖ) (K : CochainComplex X.mateModules ℤ) :=
    X.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj K))
      (derivedPullbackComplexComparison e.pullback e.left e.epsilon (P.obj.right.obj n))) ≫
      (mixedTensorRepresentative X.ring X.mateFlat (fun _ ↦ Iff.rfl)
        X.tensor b.representative K (LC.obj (P.obj.right.obj n)) (hf P n).2).hom
  have hcan (P : Y.projectionCoefficients) (n : ℕᵒᵖ)
      (K₀ : CochainComplex X.mateModules ℤ) :
      (FY P n).map (d.eta.app (RI.obj K₀)) ≫
        (π P n).app (DerivedCategory.Q.obj (RI.obj K₀)) ≫ e.right.map (nn P n (RI.obj K₀)) =
      m P n (VC.obj (RI.obj K₀)) ≫
        DerivedCategory.Q.map ((σ.app (RI.obj K₀)).app (P.obj.right.obj n)) ≫
        d.eta.app ((X.projectionTotal.obj (RI.obj K₀)).obj (LC.obj (P.obj.right.obj n))) := by
    let j (r : ℤ) := Classical.choice ((P.property n).2 r).choose_spec
    let pkg : StrictPerfectCoefficientPackage
        ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)
          (P.obj.right.obj n) :=
      { N := fun r ↦ ((P.property n).2 r).choose
        i := fun r ↦ (j r).hom
        p := fun r ↦ (j r).inv
        splitting := fun r ↦ (j r).hom_inv_id }
    exact canonicalProjectionChainSquare e a b d.eta (RI.obj K₀)
      (P.obj.right.obj n) pkg ((σ.app (RI.obj K₀)).app (P.obj.right.obj n))
      (hδ := d.derived) (computeR := d.computes) (canonicalAdj := d.counit_normalized)
      (hK := (hRI K₀).2.1) (hb := (P.property n).1)
      (hF := (hf P n).1) (hLF := (hf P n).2)
      (hf := hσ (RI.obj K₀) (P.obj.right.obj n))
  have hκ (P : Y.projectionCoefficients) (n : ℕᵒᵖ) :
      IsIso (derivedPullbackComplexComparison e.pullback e.left e.epsilon
        (P.obj.right.obj n)) := pullbackFlatComputes e _ (hf P n).1
  let κ (P : Y.projectionCoefficients) (n : ℕᵒᵖ) := (Functor.curryObj X.tensor).flip.mapIso
    (asIso (derivedPullbackComplexComparison e.pullback e.left e.epsilon
      (P.obj.right.obj n)))
  exact constructTensorTowerMorphism Y.mateModules X.mateModules
    e.pushforward LC e.right d.eta Y.projectionTotal X.projectionTotal
    Y.projectionCoefficientDiagram σ
    (QY := DerivedCategory.Q) (QX := DerivedCategory.Q)
    (QTY := DerivedCategory.Q) (QTX := DerivedCategory.Q)
    (Rt := d.Rt) (θ := d.towerEta) (evY := ly.ev) (evX := lx.ev)
    (εY := ly.evaluation) (εX := lx.evaluation) (εV := d.evaluation)
    (UY := Y.mateUnitComplex) (UX := X.mateUnitComplex)
    (ρY := Y.projectionRightUnitor) (ρX := X.projectionRightUnitor)
    (j := e.projectionUnitComplex) (augY := fun P ↦ P.obj.hom)
    (LY := ly.L) (LX := lx.L) (ηY := ly.eta) (ηX := lx.eta)
    (ordinary := d.ordinary) (a := d.a) (FY := FY)
    (FX₀ := fun P n ↦ tensorFirst X.tensor
      (DerivedCategory.Q.obj ((e.projectionCoefficientDiagram.obj P).obj n)))
    (FX := FX) (κ := κ)
    (mY := fun P n N ↦ mixedTensorRepresentative Y.ring Y.mateFlat (fun _ ↦ Iff.rfl)
      Y.tensor a.representative N (P.obj.right.obj n) (hf P n).1)
    (mX := fun P n K ↦ mixedTensorRepresentative X.ring X.mateFlat (fun _ ↦ Iff.rfl)
      X.tensor b.representative K ((e.projectionCoefficientDiagram.obj P).obj n) (hf P n).2)
    (π := π) (RI := RI) (ι := ι) (H := _) (pY := ly.p) (dY := ly.delta)
    (hY := fun f h P n ↦ tensorMapQuasiIso Y _ (hf P n).1 f h)
    (hX := fun f h P n ↦ tensorMapQuasiIso X _ (hf P n).2 f h)
    (hv := towerEvaluationNormalized e lx ly d)
    (hρY := projectionRightUnitorNaturality Y) (hρX := projectionRightUnitorNaturality X)
    (hunit := hσunit) (hordinary := d.ordinary_normalized) (ha := d.normalized)
    (hmY := fun P n ↦ mixedTensorNatIso Y a (P.obj.right.obj n) (hf P n).1)
    (hmX := fun P n ↦ mixedTensorNatIso X b
      ((e.projectionCoefficientDiagram.obj P).obj n) (hf P n).2)
    (hι := fun K ↦ (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (hRI K).1)
    (hδ := fun K ↦ d.computes (RI.obj K) (hRI K).2.1) (hcan := hcan) (hH := hf)
    (hpY := fun {_ _} v ↦ ly.p_natural v) (hdY := fun {_ _} v ↦ ly.delta_natural v)

end ProjectionConstruction

/-- The projection formula gives a natural morphism of augmented strict derived towers.

Source: Stacks Project, Cohomology on Sites, Tags 0943 (the canonical projection map)
and 0A07 (the common-direct-image comparison); Algebraization, Tag 0A0G
(blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism).

The two chain functors have comparisons in the category of diagrams of complexes.
Their factorizations through Q therefore assert independence of arbitrary representatives
in D(Tow), without identifying D(Tow) and Tow(D). The evaluation comparisons are fixed by
the existing mixed tensor representatives and the derived pullback comparison, and they
are natural in the derived variable, so they are fixed on every object (not only on
literal localizations of complexes) and the evaluated components of u are exactly alpha.
The natural transformation u is simultaneously natural in E and in every chain map of
augmented coefficient towers. Its evaluated components are exactly the counit mates.
The two final equations give the first and connecting squares of the Roos triangles;
the middle square is retained explicitly as well. The coaugmentations are normalized
through ordinary inverse limits and their total-derived comparisons.

Proof, following the eight steps of the node:
1. Use a K-injective I representing E, and N=f_*I, not a K-injective replacement of N.
   Bounded finite-free coefficients are K-flat. Localizing their total tensor towers
   gives S and T and the representative factorizations; arbitrary representatives are
   related through localization. Use def-pc-tensor-complex-sheaves and the representative
   clause of def-weil-pbc-projection-formula-arrows.
2. Apply lem-weil-pbc-ringed-topoi-derived-pullback to every coefficient complex,
   transition and augmentation to identify derived and termwise pullbacks.
3. Totalize the ordinary coefficient-natural maps t of
   def-weil-pbc-projection-formula-arrows. Their degree maps commute with both
   differentials and are the maps of lemma-weil-pbc-projection-formula-totalization.
4. Coefficient naturality makes these maps a strict map of chain towers. Localize this
   strict map and compose with the comparison to derived levelwise pushforward.
   Evaluation preserves K-injectives by its exact left adjoint, so evaluation of this
   composite is alpha, using lem-weil-ringed-tower-pushforward-limit-comparison.
5. Naturality in the coefficient tower holds before localization. A map between
   K-injective representatives represents every derived E-map; naturality of t also
   intertwines homotopies. Thus u descends naturally in both variables.
6. Apply the natural Roos triangles of
   lem-weil-pbc-ringed-strict-tower-homotopy-limit to u, including the connecting map.
7. Apply coefficient naturality to z and the tensor-unit normalization from
   lem-weil-pbc-ringed-projection-mate-exact. This gives the strict coaugmentation square
   between the constant towers and the two tensor towers.
8. Constant towers on I are K-injective: the constant functor is right adjoint to exact
   evaluation at the first level. Apply lem-weil-pbc-right-adjoint-preserves-kinjective.
   Do not assert that the constant tower on f_*I is K-injective. Naturality of the
   ordinary-limit derived comparison and the common-underived normalization of a on
   the constant tower give the asserted zeta identity. No ideal or completeness is used. -/
theorem ringedStrictTowerProjectionMorphism
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X)
    (a : RingedTensorModel Y) (b : RingedTensorModel X)
    [e.pushforward.Additive]
    [HasDerivedCategory.{w} X.projectionTowers]
    [HasDerivedCategory.{w} Y.projectionTowers]
    [HasCountableProducts X.mateDerived] [HasCountableProducts Y.mateDerived]
    (lx : StrictProjectionLimit X) (ly : StrictProjectionLimit Y)
    (d : StrictProjectionDirectImage e lx ly) :
    ∃ (CY : CochainComplex Y.mateModules ℤ ⥤
        Y.projectionCoefficients ⥤ CochainComplex Y.projectionTowers ℤ)
      (CX : CochainComplex X.mateModules ℤ ⥤
        Y.projectionCoefficients ⥤ CochainComplex X.projectionTowers ℤ)
      (cy : CY ⋙ projectionPost HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
        Y.projectionTensorDiagrams)
      (cx : CX ⋙ projectionPost HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
        e.projectionTensorDiagrams)
      (S : Y.mateDerived ⥤ Y.projectionCoefficients ⥤ DerivedCategory Y.projectionTowers)
      (T : X.mateDerived ⥤ Y.projectionCoefficients ⥤ DerivedCategory X.projectionTowers)
      (s : DerivedCategory.Q ⋙ S ≅ CY ⋙ projectionPost DerivedCategory.Q)
      (t : DerivedCategory.Q ⋙ T ≅ CX ⋙ projectionPost DerivedCategory.Q)
      (hf : ∀ (P : Y.projectionCoefficients) (n : ℕᵒᵖ),
        Y.mateFlat (P.obj.right.obj n) ∧
          X.mateFlat ((e.projectionCoefficientDiagram.obj P).obj n))
      (sEv : ∀ (M : Y.mateDerived) (P : Y.projectionCoefficients) (n : ℕᵒᵖ),
        Y.tensor.obj (M, DerivedCategory.Q.obj (P.obj.right.obj n)) ≅
          (ly.ev.obj ((S.obj M).obj P)).obj n)
      (tEv : ∀ (E : X.mateDerived) (P : Y.projectionCoefficients) (n : ℕᵒᵖ),
        X.tensor.obj (E, e.left.obj (DerivedCategory.Q.obj (P.obj.right.obj n))) ≅
          (lx.ev.obj ((T.obj E).obj P)).obj n)
      (u : e.right ⋙ S ⟶ T ⋙ projectionPost d.Rt)
      (zY : ∀ P : Y.projectionCoefficients, 𝟭 Y.mateDerived ⟶ (S.flip.obj P) ⋙ ly.L)
      (zX : ∀ P : Y.projectionCoefficients, 𝟭 X.mateDerived ⟶ (T.flip.obj P) ⋙ lx.L),
      (∀ (N : CochainComplex Y.mateModules ℤ) (P : Y.projectionCoefficients) (n : ℕᵒᵖ),
        (sEv (DerivedCategory.Q.obj N) P n).hom ≫
            (ly.ev.map ((s.hom.app N).app P)).app n ≫
            (ly.evaluation.hom.app ((CY.obj N).obj P)).app n ≫
            DerivedCategory.Q.map (((cy.hom.app N).app P).app n) =
          (mixedTensorRepresentative Y.ring Y.mateFlat (fun _ ↦ Iff.rfl)
            Y.tensor a.representative N (P.obj.right.obj n) (hf P n).1).hom) ∧
      (∀ (K : CochainComplex X.mateModules ℤ) (P : Y.projectionCoefficients) (n : ℕᵒᵖ),
        (tEv (DerivedCategory.Q.obj K) P n).hom ≫
            (lx.ev.map ((t.hom.app K).app P)).app n ≫
            (lx.evaluation.hom.app ((CX.obj K).obj P)).app n ≫
            DerivedCategory.Q.map (((cx.hom.app K).app P).app n) =
          X.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj K))
            (derivedPullbackComplexComparison e.pullback e.left e.epsilon
              (P.obj.right.obj n))) ≫
          (mixedTensorRepresentative X.ring X.mateFlat (fun _ ↦ Iff.rfl)
            X.tensor b.representative K ((e.projectionCoefficientDiagram.obj P).obj n)
              (hf P n).2).hom) ∧
      (∀ (P : Y.projectionCoefficients) (n : ℕᵒᵖ) {M M' : Y.mateDerived} (g : M ⟶ M'),
        Y.tensor.map (Prod.mkHom g (𝟙 (DerivedCategory.Q.obj (P.obj.right.obj n)))) ≫
            (sEv M' P n).hom =
          (sEv M P n).hom ≫ (ly.ev.map ((S.map g).app P)).app n) ∧
      (∀ (P : Y.projectionCoefficients) (n : ℕᵒᵖ) {E E' : X.mateDerived} (g : E ⟶ E'),
        X.tensor.map (Prod.mkHom g
            (𝟙 (e.left.obj (DerivedCategory.Q.obj (P.obj.right.obj n))))) ≫
            (tEv E' P n).hom =
          (tEv E P n).hom ≫ (lx.ev.map ((T.map g).app P)).app n) ∧
      (∀ (E : X.mateDerived) (P : Y.projectionCoefficients) (n : ℕᵒᵖ),
        (sEv (e.right.obj E) P n).hom ≫
            (ly.ev.map ((u.app E).app P)).app n ≫
            (d.evaluation.hom.app ((T.obj E).obj P)).app n =
          derivedProjectionFormulaMate e.left e.right e.derivedAdjunction Y.tensor X.tensor
            (e.tensorComparison a b) E (DerivedCategory.Q.obj (P.obj.right.obj n)) ≫
              e.right.map (tEv E P n).hom) ∧
      (∀ (N : CochainComplex Y.mateModules ℤ) (P : Y.projectionCoefficients),
        ∃ i : N ⟶ ((lim : Y.projectionTowers ⥤ Y.mateModules).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((CY.obj N).obj P),
          ProjectionCoaugmentation N P.obj.right P.obj.hom ((CY.obj N).obj P)
            ((Functor.mapIso ((CategoryTheory.evaluation Y.projectionCoefficients _).obj P)
              (cy.app N))) i ∧
          (zY P).app (DerivedCategory.Q.obj N) ≫ ly.L.map ((s.hom.app N).app P) =
            DerivedCategory.Q.map i ≫ ly.eta.app ((CY.obj N).obj P)) ∧
      (∀ (K : CochainComplex X.mateModules ℤ) (P : Y.projectionCoefficients),
        ∃ (z : (Functor.const ℕᵒᵖ).obj X.mateUnitComplex ⟶
            e.projectionCoefficientDiagram.obj P)
          (i : K ⟶ ((lim : X.projectionTowers ⥤ X.mateModules).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((CX.obj K).obj P)),
          (∀ n : ℕᵒᵖ, z.app n = e.projectionUnitComplex.inv ≫
            (e.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).map (P.obj.hom.app n)) ∧
          ProjectionCoaugmentation K (e.projectionCoefficientDiagram.obj P) z
            ((CX.obj K).obj P)
            ((Functor.mapIso ((CategoryTheory.evaluation Y.projectionCoefficients _).obj P)
              (cx.app K))) i ∧
          (zX P).app (DerivedCategory.Q.obj K) ≫ lx.L.map ((t.hom.app K).app P) =
            DerivedCategory.Q.map i ≫ lx.eta.app ((CX.obj K).obj P)) ∧
      (∀ (E : X.mateDerived) (P : Y.projectionCoefficients),
        (zY P).app (e.right.obj E) ≫ ly.L.map ((u.app E).app P) =
          e.right.map ((zX P).app E) ≫ d.a.hom.app ((T.obj E).obj P)) ∧
      (∀ (E : X.mateDerived) (P : Y.projectionCoefficients),
        ly.L.map ((u.app E).app P) ≫ ly.p (d.Rt.obj ((T.obj E).obj P)) =
          ly.p ((S.obj (e.right.obj E)).obj P) ≫
            Limits.Pi.map (fun n : ℕ ↦ (ly.ev.map ((u.app E).app P)).app (op n))) ∧
      (∀ (E : X.mateDerived) (P : Y.projectionCoefficients),
        Limits.Pi.map (fun n : ℕ ↦ (ly.ev.map ((u.app E).app P)).app (op n)) ≫
            towerTransitionEndomorphism (fun n : ℕ ↦
              (ly.ev.obj (d.Rt.obj ((T.obj E).obj P))).map
                (homOfLE (Nat.le_succ n)).op) =
          towerTransitionEndomorphism (fun n : ℕ ↦
            (ly.ev.obj ((S.obj (e.right.obj E)).obj P)).map
              (homOfLE (Nat.le_succ n)).op) ≫
            Limits.Pi.map (fun n : ℕ ↦ (ly.ev.map ((u.app E).app P)).app (op n))) ∧
      (∀ (E : X.mateDerived) (P : Y.projectionCoefficients),
        Limits.Pi.map (fun n : ℕ ↦ (ly.ev.map ((u.app E).app P)).app (op n)) ≫
            ly.delta (d.Rt.obj ((T.obj E).obj P)) =
          ly.delta ((S.obj (e.right.obj E)).obj P) ≫
            (ly.L.map ((u.app E).app P))⟦(1 : ℤ)⟧') := by
  exact buildTowerProjection e a b lx ly d


end SheafOfModules
