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
import Sheaf.Paper.ProjectionFormulaTotalization
import Sheaf.Paper.ProEtaleProjectionFormulaArrows
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.CategoryTheory.Abelian.FunctorCategory

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

/-- The total right derived inverse limit with its comparison, evaluation and Roos triangle.
This is precisely the data supplied by the strict-tower homotopy-limit dependency.
Source: Stacks 0A07, 0940, 0941
(blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
structure StrictProjectionLimit (A : RingedTensorCorner.{u, w})
    [HasDerivedCategory.{w} A.projectionTowers]
    [HasCountableProducts A.mateDerived] where
  L : DerivedCategory A.projectionTowers ⥤ A.mateDerived
  eta : (lim : A.projectionTowers ⥤ A.mateModules).mapHomologicalComplex
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ L
  derived : L.IsRightDerivedFunctor eta
    (HomologicalComplex.quasiIso A.projectionTowers (ComplexShape.up ℤ))
  computes : ∀ I : CochainComplex A.projectionTowers ℤ, I.IsKInjective → IsIso (eta.app I)
  ev : DerivedCategory A.projectionTowers ⥤ (ℕᵒᵖ ⥤ A.mateDerived)
  evaluation : DerivedCategory.Q ⋙ ev ≅
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ projectionPost DerivedCategory.Q
  p : ∀ Z, L.obj Z ⟶ ∏ᶜ fun n : ℕ ↦ (ev.obj Z).obj (op n)
  delta : ∀ Z, (∏ᶜ fun n : ℕ ↦ (ev.obj Z).obj (op n)) ⟶ (L.obj Z)⟦(1 : ℤ)⟧
  roos : ∀ Z, IsDerivedLimitTriangle
    (fun n : ℕ ↦ (ev.obj Z).map (homOfLE (Nat.le_succ n)).op) (L.obj Z) (p Z) (delta Z)
  p_natural : ∀ {Z W} (v : Z ⟶ W),
    L.map v ≫ p W = p Z ≫ Limits.Pi.map (fun n : ℕ ↦ (ev.map v).app (op n))
  delta_natural : ∀ {Z W} (v : Z ⟶ W),
    Limits.Pi.map (fun n : ℕ ↦ (ev.map v).app (op n)) ≫ delta W =
      delta Z ≫ (L.map v)⟦(1 : ℤ)⟧'

/-- Levelwise module direct image and its action on complexes of strict towers.
Source: Stacks 0A07 (blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
abbrev RingedTensorEdge.projectionTowerPushforward
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X) :=
  (Functor.whiskeringRight ℕᵒᵖ X.mateModules Y.mateModules).obj e.pushforward

/-- The common-direct-image comparison, with its underived normalization.
This packages the specified comparison of the pushforward/limit dependency, not an
arbitrary isomorphism. Evaluation is normalized on K-injective tower complexes.
Source: Stacks 0A07, 0940
(blueprint: lem-weil-pbc-ringed-strict-tower-projection-morphism). -/
structure StrictProjectionDirectImage {Y X : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge Y X) [e.pushforward.Additive]
    [HasDerivedCategory.{w} X.projectionTowers]
    [HasDerivedCategory.{w} Y.projectionTowers]
    [HasCountableProducts X.mateDerived] [HasCountableProducts Y.mateDerived]
    (lx : StrictProjectionLimit X) (ly : StrictProjectionLimit Y) where
  eta : e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ e.right
  derived : e.right.IsRightDerivedFunctor eta
    (HomologicalComplex.quasiIso X.mateModules (ComplexShape.up ℤ))
  computes : ∀ I : CochainComplex X.mateModules ℤ, I.IsKInjective → IsIso (eta.app I)
  counit_normalized : ∀ I : CochainComplex X.mateModules ℤ, I.IsKInjective →
    e.left.map (eta.app I) ≫ e.derivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
      derivedPullbackComplexComparison e.pullback e.left e.epsilon
        ((e.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
      DerivedCategory.Q.map
        ((e.moduleAdjunction.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I)
  Rt : DerivedCategory X.projectionTowers ⥤ DerivedCategory Y.projectionTowers
  towerEta : e.projectionTowerPushforward.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Rt
  towerDerived : Rt.IsRightDerivedFunctor towerEta
    (HomologicalComplex.quasiIso X.projectionTowers (ComplexShape.up ℤ))
  towerComputes : ∀ I : CochainComplex X.projectionTowers ℤ,
    I.IsKInjective → IsIso (towerEta.app I)
  evaluation : Rt ⋙ ly.ev ≅ lx.ev ⋙ projectionPost e.right
  evaluation_normalized : ∀ (I : CochainComplex X.projectionTowers ℤ), I.IsKInjective →
    ∀ n : ℕᵒᵖ,
      (ly.ev.map (towerEta.app I)).app n ≫
          (evaluation.hom.app (DerivedCategory.Q.obj I)).app n ≫
          e.right.map ((lx.evaluation.hom.app I).app n) =
        (ly.evaluation.hom.app
          ((e.projectionTowerPushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).app n ≫
          eta.app (I.asFunctor.obj n)
  ordinary : (lim : X.projectionTowers ⥤ X.mateModules) ⋙ e.pushforward ≅
    e.projectionTowerPushforward ⋙ (lim : Y.projectionTowers ⥤ Y.mateModules)
  ordinary_normalized : ∀ H, ordinary.hom.app H = limit.post H e.pushforward
  a : lx.L ⋙ e.right ≅ Rt ⋙ ly.L
  normalized : ∀ I : CochainComplex X.projectionTowers ℤ,
    eta.app (((lim : X.projectionTowers ⥤ X.mateModules).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) ≫ e.right.map (lx.eta.app I) ≫
        a.hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom
        (ComplexShape.up ℤ)).app I) ≫
        ly.eta.app ((e.projectionTowerPushforward.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) ≫ ly.L.map (towerEta.app I)

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
  sorry

end SheafOfModules
