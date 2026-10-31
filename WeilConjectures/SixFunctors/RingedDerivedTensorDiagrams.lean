/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RingedDerivedComparisonData
import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherenceSupplement
import WeilConjectures.AlgebraicGeometry.FiniteDerivedTensorModels
import all WeilConjectures.AlgebraicGeometry.ProjectionMateExact
import all WeilConjectures.Algebra.Homology.RingedForgetTensorAssociatorRepresentatives
import all WeilConjectures.Algebra.Homology.RingedForgetTensorCoherence
import all WeilConjectures.Algebra.Homology.RingedForgetTensorUnitRightRepresentatives
import all WeilConjectures.Algebra.Homology.RingedOrdinaryEvaluationLocalization
import all WeilConjectures.Algebra.Homology.RingedTensorConstraintCompletion
import all WeilConjectures.Algebra.Homology.RingedKFlatNativeModelIdentification
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModelSupplement

/-! # Coherence equations for the explicit canonical derived comparisons

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0FPT.
(blueprint: lem-sfb-ringed-derived-tensor-diagrams).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  WeilConjectures SheafOfModules
namespace CategoryTheory.RingedDerivedComparisons


/-- The localized scalar-action unit map, with no choice of monoidal structure.
Source: Stacks Project, Cohomology on Sites, Tag 07A4; Modules on Sites, Tag 03EL.
(blueprint: lem-sfb-ringed-derived-tensor-diagrams). -/
def canonicalDerivedUnitComparison {X Y : Site.{u, w}}
    (e : RingedTensorEdge Y.corner X.corner)
    (j : e.pullback.obj (SheafOfModules.unit Y.ring) ≅ SheafOfModules.unit X.ring) :
    e.left.obj Y.closed.monoidal.tensorUnit ⟶ X.closed.monoidal.tensorUnit :=
  e.left.map Y.coherence.unitIso.hom ≫
    derivedPullbackComplexComparison e.pullback e.left e.epsilon
      (ringedTensorUnitComplex.{u, u, u} Y.J Y.A) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        e.pullback (ComplexShape.up ℤ) 0).hom.app (SheafOfModules.unit Y.ring) ≫
        (CochainComplex.singleFunctor X.modules 0).map j.hom) ≫
    X.coherence.unitIso.inv

/-- The three oplax coherence diagrams and the signed symmetry equation for the
specified comparison maps. Naturality is already supplied by tensorComparison.
Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0FPT.
(blueprint: lem-sfb-ringed-derived-tensor-diagrams). -/
def CanonicalTensorDiagrams {X Y : Site.{u, w}}
    (e : RingedTensorEdge Y.corner X.corner)
    (rY : RingedTensorModel Y.corner) (rX : RingedTensorModel X.corner)
    (j : e.pullback.obj (SheafOfModules.unit Y.ring) ≅ SheafOfModules.unit X.ring) : Prop :=
  letI : MonoidalCategory Y.D := Y.closed.monoidal
  letI : MonoidalCategory X.D := X.closed.monoidal
  let F : Y.D ⥤ X.D := e.left
  let t : ∀ U V : Y.D, F.obj (U ⊗ V) ≅ F.obj U ⊗ F.obj V :=
    fun U V ↦ (e.tensorComparison rY rX).app (U, V)
  let a : F.obj (𝟙_ Y.D) ⟶ 𝟙_ X.D := canonicalDerivedUnitComparison e j
  IsIso a ∧
  (∀ U V W : Y.D,
    (t (U ⊗ V) W).hom ≫ (t U V).hom ▷ F.obj W ≫
        (α_ (F.obj U) (F.obj V) (F.obj W)).hom =
      F.map (α_ U V W).hom ≫ (t U (V ⊗ W)).hom ≫
        F.obj U ◁ (t V W).hom) ∧
  (∀ U : Y.D, (λ_ (F.obj U)).inv =
    F.map (λ_ U).inv ≫ (t (𝟙_ Y.D) U).hom ≫ a ▷ F.obj U) ∧
  (∀ U : Y.D, (ρ_ (F.obj U)).inv =
    F.map (ρ_ U).inv ≫ (t U (𝟙_ Y.D)).hom ≫ F.obj U ◁ a) ∧
  (∀ U V : Y.D,
    (t U V).hom ≫
        (X.symmetry.toBraidedCategory.braiding (F.obj U) (F.obj V)).hom =
      F.map (Y.symmetry.toBraidedCategory.braiding U V).hom ≫ (t V U).hom)

attribute [local instance 100000] HomologicalComplex.monoidalCategoryStruct
attribute [local irreducible] SheafOfModules.monoidalCategory
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q
  sheafCompose CommRingCat.hasForgetToRingCat
  homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolutionIso

attribute [local instance] SheafOfModules.monoidalCategory
attribute [local semireducible] SheafOfModules.monoidalCategory
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q sheafCompose
  CommRingCat.hasForgetToRingCat

universe u₁ v₁ u₂ v₂

private theorem left_from_right {B : Type u₁} [Category.{v₁} B] [MonoidalCategory B]
    [BraidedCategory B] {A : Type u₂} [Category.{v₂} A] [MonoidalCategory A]
    [BraidedCategory A] (F : B ⥤ A)
    (μ : ∀ X Y : B, F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y)
    (a : F.obj (𝟙_ B) ⟶ 𝟙_ A)
    (hβ : ∀ X Y : B, F.map (β_ X Y).hom ≫ μ Y X =
      μ X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
    (hr : ∀ X : B, μ X (𝟙_ B) ≫ F.obj X ◁ a ≫ (ρ_ (F.obj X)).hom =
      F.map (ρ_ X).hom) (X : B) :
    μ (𝟙_ B) X ≫ a ▷ F.obj X ≫ (λ_ (F.obj X)).hom = F.map (λ_ X).hom := by
  calc
    _ = μ (𝟙_ B) X ≫ (β_ (F.obj (𝟙_ B)) (F.obj X)).hom ≫
        F.obj X ◁ a ≫ (ρ_ (F.obj X)).hom := by
      rw [← BraidedCategory.braiding_naturality_left_assoc, braiding_rightUnitor]
    _ = F.map (β_ (𝟙_ B) X).hom ≫ μ X (𝟙_ B) ≫
        F.obj X ◁ a ≫ (ρ_ (F.obj X)).hom := by
      rw [← reassoc_of% (hβ (𝟙_ B) X)]
    _ = _ := by
      rw [hr, ← F.map_comp, braiding_rightUnitor]

set_option maxHeartbeats 1000000 in
-- Infer the total tensor on the explicit coefficient-module category.
private theorem coefficient_map_tensor (Z : Site.{u, w})
    {P P' Q Q' : CochainComplex Z.modules ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    letI : MonoidalCategory Z.modules := SheafOfModules.monoidalCategory Z.A
    (coefficientTotalTensor.{u, u, u} Z.J Z.A).map
      (X := (P, Q)) (Y := (P', Q')) (f, g) = f ⊗ₘ g := by
  let : MonoidalCategory Z.modules := SheafOfModules.monoidalCategory Z.A
  exact RingedForgetTensorTransposition.total_map_generic
    (curriedTensor Z.modules) f g

private theorem ordinary_associator_eq (Z : Site.{u, w})
    (P Q N : CochainComplex Z.modules ℤ) :
    letI : MonoidalCategory Z.modules := SheafOfModules.monoidalCategory Z.A
    (ordinaryAssociator.{u, u, u} Z.J Z.A P Q N).hom = (α_ P Q N).hom := by
  let : MonoidalCategory Z.modules := SheafOfModules.monoidalCategory Z.A
  rfl

private def edgePullback {X Y : Site.{u, w}}
    (e : RingedTensorEdge Y.corner X.corner) :
    CochainPullback.RingedPullback.{u, u, u, u, u} Y.A X.A where
  uInv := e.inverse
  uPush := e.direct
  adj := e.adjunction
  finiteLimits := e.finiteLimits
  RI := e.inverseRing
  I := e.algebraic
  coefficient := e.ringMap
  L := e.pullback
  hobj := e.object_eq
  hmap := e.map_eq
  V := e.pushforward
  moduleAdj := e.moduleAdjunction
  additive := e.additive

private def edgeComparison {X Y : Site.{u, w}}
    (e : RingedTensorEdge Y.corner X.corner) :
    CochainPullback.Comparison.{u, u, u, u, u}
      (edgePullback.{u, w} (X := X) (Y := Y) e) :=
  { q := e.ordinaryTensor.q
    q_one := e.ordinaryTensor.q_one
    mu := e.ordinaryTensor.mu
    naturality := e.ordinaryTensor.naturality
    pure := e.ordinaryTensor.pure }

private def edgeAlpha {X Y : Site.{u, w}}
    (e : RingedTensorEdge Y.corner X.corner) :
    DerivedCategory.Q.{w} ⋙ e.left ⟶
      e.pullback.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso Y.modules).inv e.left ≫
    Functor.whiskerLeft (HomotopyCategory.quotient Y.modules (.up ℤ)) e.epsilon ≫
    Functor.whiskerRight (e.pullback.mapHomotopyCategoryFactors (.up ℤ)).hom
      DerivedCategory.Qh.{w} ≫
    Functor.whiskerLeft (e.pullback.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso X.modules).hom

private theorem edgeAlpha_eq {X Y : Site.{u, w}}
    (e : RingedTensorEdge Y.corner X.corner) (P : CochainComplex Y.modules ℤ) :
    derivedPullbackComplexComparison e.pullback e.left e.epsilon P =
      (edgeAlpha e).app P := rfl

set_option maxHeartbeats 800000 in
-- Normalize the dependent ringed-site representative comparison equations.
private theorem edgeAlpha_iso {X Y : Site.{u, w}}
    (e : RingedTensorEdge Y.corner X.corner) (P : CochainComplex Y.modules ℤ)
    (hP : Y.corner.mateFlat P) : IsIso ((edgeAlpha e).app P) := by
  dsimp only [Site.corner] at e
  dsimp only [Site.corner] at *
  let := e.finiteLimits
  let := e.additive
  obtain ⟨L, ε, hL, _, _, hε, _⟩ := ringedTopoiDerivedPullback.{u, w}
    e.inverse e.direct e.adjunction e.algebraic e.ringMap e.pullback e.object_eq e.map_eq
  have := hL
  let : e.left.IsLeftDerivedFunctor e.epsilon
      (HomotopyCategory.quasiIso Y.modules (.up ℤ)) := e.isLeftDerived
  let a := Functor.leftDerivedNatIso (L := DerivedCategory.Qh.{w} (C := Y.modules))
    L e.left ε e.epsilon
    (HomotopyCategory.quasiIso Y.modules (.up ℤ)) (Iso.refl _)
  have : IsIso (ε.app ((HomotopyCategory.quotient Y.modules (.up ℤ)).obj P)) :=
    hε P hP.1 hP.2
  have hfac : a.hom.app (DerivedCategory.Qh.{w}.obj
      ((HomotopyCategory.quotient Y.modules (.up ℤ)).obj P)) ≫
      e.epsilon.app ((HomotopyCategory.quotient Y.modules (.up ℤ)).obj P) =
      ε.app ((HomotopyCategory.quotient Y.modules (.up ℤ)).obj P) := by
    simpa only [a, Functor.leftDerivedNatIso_hom, Iso.refl_hom, NatTrans.id_app,
      Category.comp_id] using Functor.leftDerivedNatTrans_app L e.left ε e.epsilon
        (HomotopyCategory.quasiIso Y.modules (.up ℤ)) (𝟙 _)
        ((HomotopyCategory.quotient Y.modules (.up ℤ)).obj P)
  have : IsIso (e.epsilon.app
      ((HomotopyCategory.quotient Y.modules (.up ℤ)).obj P)) := by
    have : IsIso (a.hom.app _ ≫ e.epsilon.app
        ((HomotopyCategory.quotient Y.modules (.up ℤ)).obj P)) := by
      rw [hfac]
      infer_instance
    exact IsIso.of_isIso_comp_left (a.hom.app _) (e.epsilon.app _)
  dsimp only [edgeAlpha, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

section Representatives
variable {X Y : Site.{u, w}} (e : RingedTensorEdge Y.corner X.corner)
  (rY : RingedTensorModel Y.corner) (rX : RingedTensorModel X.corner)
  (hY : ∀ P Q hP hQ,
    rY.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
      (Y.model.iso Y.J Y.A Y.closed P Q hP.1 hQ.1).hom)
  (hX : ∀ P Q hP hQ,
    rX.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
      (X.model.iso X.J X.A X.closed P Q hP.1 hQ.1).hom)

set_option maxHeartbeats 800000 in
-- Normalize the dependent ringed-site representative comparison equations.
include hY hX in
private theorem edge_model_square (P Q : CochainComplex Y.modules ℤ)
    (hp : Y.corner.mateFlat P) (hq : Y.corner.mateFlat Q) :
    ∃ (hp' : X.corner.mateFlat ((e.pullback.mapHomologicalComplex (.up ℤ)).obj P))
      (hq' : X.corner.mateFlat ((e.pullback.mapHomologicalComplex (.up ℤ)).obj Q)),
      e.left.map (Y.model.iso Y.J Y.A Y.closed P Q hp.1 hq.1).hom ≫
        (e.tensorComparison rY rX).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        X.closed.tensor.map (Prod.mkHom ((edgeAlpha e).app P) ((edgeAlpha e).app Q)) =
      (edgeAlpha e).app ((coefficientTotalTensor.{u, u, u} Y.J Y.A).obj (P, Q)) ≫
        DerivedCategory.Q.map (CochainPullback.comparison
          (edgePullback.{u, w} (X := X) (Y := Y) e) (edgeComparison e) P Q).hom ≫
        (X.model.iso X.J X.A X.closed _ _ hp'.1 hq'.1).hom := by
  dsimp only [Site.corner] at *
  obtain ⟨hp', hq', hh⟩ := matePullbackComparisonSquare e rY rX P Q hp hq
  refine ⟨hp', hq', ?_⟩
  dsimp only [RingedTensorModel.mateRepresentative] at hh
  erw [hY, hX] at hh
  simp only [edgeAlpha_eq] at hh
  have hc := FiniteDerivedTensorModels.legacy_comparison_eq
    (edgePullback.{u, w} (X := X) (Y := Y) e) (edgeComparison e) P Q
  change (e.ordinaryTensor.totalIso _ _ _ _ _ _ _ _ _ _ P Q).inv = _ at hc
  simp only [Functor.mapIso_inv] at hh
  erw [hc] at hh
  exact hh

include rY rX hY hX in
private theorem edge_resolving (P : CochainComplex Y.modules ℤ)
    (hp : P.IsKFlatIndependentCoefficients)
    (fp : ∀ n : ℤ, IsFlatOnSite (J := Y.J) (R := Y.A) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients (J := X.J) (R := X.A)
        ((e.pullback.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ n : ℤ, IsFlatOnSite (J := X.J) (R := X.A) (e.pullback.obj (P.X n)) := by
  dsimp only [Site.corner] at *
  have hp' := (FiniteDerivedTensorModels.resolving_native Y P).1 ⟨hp, fp⟩
  obtain ⟨h, _, _⟩ := edge_model_square e rY rX hY hX P P hp' hp'
  exact (FiniteDerivedTensorModels.resolving_native X _).2 h

private theorem edge_alpha_isIso (P : CochainComplex Y.modules ℤ)
    (hp : P.IsKFlatIndependentCoefficients)
    (fp : ∀ n : ℤ, IsFlatOnSite (J := Y.J) (R := Y.A) (P.X n)) :
    IsIso ((edgeAlpha e).app P) :=
  edgeAlpha_iso e P ((FiniteDerivedTensorModels.resolving_native Y P).1 ⟨hp, fp⟩)

set_option maxHeartbeats 800000 in
-- Normalize the dependent ringed-site representative comparison equations.
include hY hX in
private theorem edge_square (P Q : CochainComplex Y.modules ℤ)
    (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
    (hfp : ∀ n : ℤ, IsFlatOnSite (J := Y.J) (R := Y.A) (P.X n))
    (hfq : ∀ n : ℤ, IsFlatOnSite (J := Y.J) (R := Y.A) (Q.X n))
    (hp' : CochainComplex.IsKFlatIndependentCoefficients (J := X.J) (R := X.A)
      ((e.pullback.mapHomologicalComplex (.up ℤ)).obj P))
    (hq' : CochainComplex.IsKFlatIndependentCoefficients (J := X.J) (R := X.A)
      ((e.pullback.mapHomologicalComplex (.up ℤ)).obj Q)) :
    e.left.map (Y.model.iso Y.J Y.A Y.closed P Q hp hq).hom ≫
      (e.tensorComparison rY rX).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      X.closed.tensor.map (Prod.mkHom ((edgeAlpha e).app P) ((edgeAlpha e).app Q)) =
    (edgeAlpha e).app ((coefficientTotalTensor.{u, u, u} Y.J Y.A).obj (P, Q)) ≫
      DerivedCategory.Q.map
        (CochainPullback.comparison (edgePullback.{u, w} (X := X) (Y := Y) e) (edgeComparison e) P
          Q).hom ≫
      (X.model.iso X.J X.A X.closed _ _ hp' hq').hom := by
  dsimp only [Site.corner] at *
  obtain ⟨_, _, hh⟩ := edge_model_square e rY rX hY hX P Q
    ((FiniteDerivedTensorModels.resolving_native Y P).1 ⟨hp, hfp⟩)
    ((FiniteDerivedTensorModels.resolving_native Y Q).1 ⟨hq, hfq⟩)
  exact hh

local instance : MonoidalCategory Y.modules := SheafOfModules.monoidalCategory Y.A
local instance : MonoidalCategory X.modules := SheafOfModules.monoidalCategory X.A


set_option maxHeartbeats 1600000 in
-- Normalize the dependent ringed-site representative comparison equations.
include hY hX in
private theorem edge_associativity (P Q N : CochainComplex Y.modules ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (fP : ∀ n : ℤ, IsFlatOnSite (J := Y.J) (R := Y.A) (P.X n))
    (hQ : Q.IsKFlatIndependentCoefficients)
    (fQ : ∀ n : ℤ, IsFlatOnSite (J := Y.J) (R := Y.A) (Q.X n))
    (hN : N.IsKFlatIndependentCoefficients)
    (fN : ∀ n : ℤ, IsFlatOnSite (J := Y.J) (R := Y.A) (N.X n)) :
    letI : MonoidalCategory (DerivedCategory.{w} Y.corner.mateModules) := Y.closed.monoidal
    letI : MonoidalCategory (DerivedCategory.{w} X.corner.mateModules) := X.closed.monoidal
    letI : MonoidalCategory (DerivedCategory.{w} Y.modules) := Y.closed.monoidal
    letI : MonoidalCategory (DerivedCategory.{w} X.modules) := X.closed.monoidal
    e.left.map (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
        (DerivedCategory.Q.obj N)).hom ≫
      (e.tensorComparison rY rX).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj N) ≫
      e.left.obj (DerivedCategory.Q.obj P) ◁
        (e.tensorComparison rY rX).hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N) =
    (e.tensorComparison rY rX).hom.app
        (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N) ≫
      (e.tensorComparison rY rX).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ▷
        e.left.obj (DerivedCategory.Q.obj N) ≫
      (α_ (e.left.obj (DerivedCategory.Q.obj P)) (e.left.obj (DerivedCategory.Q.obj Q))
        (e.left.obj (DerivedCategory.Q.obj N))).hom := by
  dsimp only [Site.corner] at *
  let F : Y.D ⥤ X.D := e.left
  let : MonoidalCategory Y.D := Y.closed.monoidal
  let : MonoidalCategory X.D := X.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} Y.corner.mateModules) := Y.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} X.corner.mateModules) := X.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} Y.modules) := Y.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} X.modules) := X.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} (CochainPullback.Modules.{u, u, u} Y.A)) :=
    Y.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} (CochainPullback.Modules.{u, u, u} X.A)) :=
    X.closed.monoidal
  let := e.additive
  let V : CochainComplex Y.modules ℤ ⥤ CochainComplex X.modules ℤ :=
    e.pullback.mapHomologicalComplex (.up ℤ)
  let B := coefficientTotalTensor.{u, u, u} Y.J Y.A
  let A := coefficientTotalTensor.{u, u, u} X.J X.A
  let μ : Y.closed.tensor ⋙ F ≅ F.prod F ⋙ X.closed.tensor :=
    e.tensorComparison rY rX
  change F.map (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
        (DerivedCategory.Q.obj N)).hom ≫
      μ.hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj N) ≫
      F.obj (DerivedCategory.Q.obj P) ◁
        μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N) =
    μ.hom.app
        (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N) ≫
      μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ▷
        F.obj (DerivedCategory.Q.obj N) ≫
      (α_ (F.obj (DerivedCategory.Q.obj P)) (F.obj (DerivedCategory.Q.obj Q))
        (F.obj (DerivedCategory.Q.obj N))).hom
  let chain : ∀ P Q : CochainComplex Y.modules ℤ,
      V.obj (B.obj (P, Q)) ≅ A.obj (V.obj P, V.obj Q) :=
    fun P Q ↦ CochainPullback.comparison (edgePullback e) (edgeComparison e) P Q
  have hU := edge_resolving e rY rX hY hX
  have hμ := edge_square e rY rX hY hX
  let PQ := B.obj (P, Q)
  let QN := B.obj (Q, N)
  have hPQ := coefficientTotalTensor_isKFlat.{u, u, u} Y.J Y.A P Q hP hQ
  have hQN := coefficientTotalTensor_isKFlat.{u, u, u} Y.J Y.A Q N hQ hN
  have fPQ : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u}
      (J := Y.J) (R := Y.A) (PQ.X i) := by
    dsimp only [PQ, B]
    rw [RingedForgetTensorTransposition.coefficient_total_eq]
    exact (SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
      Y.A P Q hP hQ fP fQ).2.1
  have fQN : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u, u, u, u}
      (J := Y.J) (R := Y.A) (QN.X i) := by
    dsimp only [QN, B]
    rw [RingedForgetTensorTransposition.coefficient_total_eq]
    exact (SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
      Y.A Q N hQ hN fQ fN).2.1
  have hUP : (V.obj P).IsKFlatIndependentCoefficients := (hU P hP fP).1
  have hUQ : (V.obj Q).IsKFlatIndependentCoefficients := (hU Q hQ fQ).1
  have hUN : (V.obj N).IsKFlatIndependentCoefficients := (hU N hN fN).1
  have hUPQ : (V.obj PQ).IsKFlatIndependentCoefficients := (hU PQ hPQ fPQ).1
  have hUQN : (V.obj QN).IsKFlatIndependentCoefficients := (hU QN hQN fQN).1
  have hAPQ := coefficientTotalTensor_isKFlat.{u, u, u} X.J X.A (V.obj P) (V.obj Q) hUP hUQ
  have hAQN := coefficientTotalTensor_isKFlat.{u, u, u} X.J X.A (V.obj Q) (V.obj N) hUQ hUN
  let aB := α_ P Q N
  let aA := α_ (V.obj P) (V.obj Q) (V.obj N)
  have heB := RingedKFlatModel.associator_model_native.{u, u, u, w}
    Y.J Y.A Y.closed Y.model Y.symmetry Y.coherence P Q N hP hQ hN
  have heA := RingedKFlatModel.associator_model_native.{u, u, u, w}
    X.J X.A X.closed X.model X.symmetry X.coherence
    (V.obj P) (V.obj Q) (V.obj N) hUP hUQ hUN
  have hc := (CochainPullback.cochainPullbackTensorCoherence.{u, u, u, u, u, u, u}
    (edgePullback.{u, w} (X := X) (Y := Y) e) (edgeComparison e)).1.2.1 P Q N
  simp only [id_tensorHom, tensorHom_id] at hc
  change V.map aB.hom ≫ (chain P QN).hom ≫
      (V.obj P ◁ (chain Q N).hom) =
    (chain PQ N).hom ≫ ((chain P Q).hom ▷ V.obj N) ≫ aA.hom at hc
  rw [show Y.coherence.tensorIso PQ N (Or.inr hN) = Y.model.iso Y.J Y.A Y.closed PQ N hPQ hN from
      Y.coherence.tensorIso_both PQ N hPQ hN,
    Y.coherence.tensorIso_both P QN hP hQN] at heB
  rw [show X.coherence.tensorIso (A.obj (V.obj P, V.obj Q)) (V.obj N) (Or.inr hUN) =
      X.model.iso X.J X.A X.closed _ _ hAPQ hUN from X.coherence.tensorIso_both _ _ hAPQ hUN,
    X.coherence.tensorIso_both (V.obj P) (A.obj (V.obj Q, V.obj N)) hUP hAQN] at heA
  let bPQ := Y.model.iso Y.J Y.A Y.closed P Q hP hQ
  let bQN := Y.model.iso Y.J Y.A Y.closed Q N hQ hN
  let bL := Y.model.iso Y.J Y.A Y.closed PQ N hPQ hN
  let bR := Y.model.iso Y.J Y.A Y.closed P QN hP hQN
  let aPQ := X.model.iso X.J X.A X.closed (V.obj P) (V.obj Q) hUP hUQ
  let aQN := X.model.iso X.J X.A X.closed (V.obj Q) (V.obj N) hUQ hUN
  let aL := X.model.iso X.J X.A X.closed (A.obj (V.obj P, V.obj Q)) (V.obj N) hAPQ hUN
  let aR := X.model.iso X.J X.A X.closed (V.obj P) (A.obj (V.obj Q, V.obj N)) hUP hAQN
  let aL₀ := X.model.iso X.J X.A X.closed (V.obj PQ) (V.obj N) hUPQ hUN
  let aR₀ := X.model.iso X.J X.A X.closed (V.obj P) (V.obj QN) hUP hUQN
  let lB := bL ≪≫ whiskerRightIso bPQ (DerivedCategory.Q.obj N)
  let rB := bR ≪≫ whiskerLeftIso (DerivedCategory.Q.obj P) bQN
  let lA := aL ≪≫ whiskerRightIso aPQ (DerivedCategory.Q.obj (V.obj N))
  let rA := aR ≪≫ whiskerLeftIso (DerivedCategory.Q.obj (V.obj P)) aQN
  let ε : DerivedCategory.Q.{w} ⋙ F ⟶ V ⋙ DerivedCategory.Q.{w} := edgeAlpha e
  have := edge_alpha_isIso e P hP fP
  have := edge_alpha_isIso e Q hQ fQ
  have := edge_alpha_isIso e N hN fN
  let tPQ := DerivedCategory.Q.map ((chain P Q).hom)
  let tQN := DerivedCategory.Q.map ((chain Q N).hom)
  let tL := DerivedCategory.Q.map ((chain PQ N).hom)
  let tR := DerivedCategory.Q.map ((chain P QN).hom)
  let eL := ε.app (B.obj (PQ, N)) ≫ tL ≫
    DerivedCategory.Q.map (A.map (X := (V.obj PQ, V.obj N))
      (Y := (A.obj (V.obj P, V.obj Q), V.obj N))
      ((chain P Q).hom, 𝟙 (V.obj N)))
  let eR := ε.app (B.obj (P, QN)) ≫ tR ≫
    DerivedCategory.Q.map (A.map (X := (V.obj P, V.obj QN))
      (Y := (V.obj P, A.obj (V.obj Q, V.obj N)))
      (𝟙 (V.obj P), (chain Q N).hom))
  have hB : lB.hom ≫ (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
        (DerivedCategory.Q.obj N)).hom = DerivedCategory.Q.map aB.hom ≫ rB.hom := by
    with_unfolding_all
      simpa only [aB, ordinary_associator_eq Y P Q N, lB, rB, bL, bR, bPQ, bQN,
        PQ, QN, B, Iso.trans_hom,
        whiskerRightIso_hom, whiskerLeftIso_hom,
      CoefficientClosedStructure.tensor, tensor_map, tensorHom_id, id_tensorHom,
      Category.assoc] using heB
  have hA : lA.hom ≫ (α_ (DerivedCategory.Q.obj (V.obj P))
        (DerivedCategory.Q.obj (V.obj Q)) (DerivedCategory.Q.obj (V.obj N))).hom =
      DerivedCategory.Q.map aA.hom ≫ rA.hom := by
    with_unfolding_all
      simpa only [aA, ordinary_associator_eq X (V.obj P) (V.obj Q) (V.obj N),
        lA, rA, aL, aR, aPQ, aQN, A, Iso.trans_hom,
        whiskerRightIso_hom, whiskerLeftIso_hom,
      CoefficientClosedStructure.tensor, tensor_map, tensorHom_id, id_tensorHom,
      Category.assoc] using heA
  have hmPQ := hμ P Q hP hQ fP fQ hUP hUQ
  have hmQN := hμ Q N hQ hN fQ fN hUQ hUN
  have hmL := hμ PQ N hPQ hN fPQ fN hUPQ hUN
  have hmR := hμ P QN hP hQN fP fQN hUP hUQN
  change F.map bPQ.hom ≫ μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      X.closed.tensor.map (Prod.mkHom (ε.app P) (ε.app Q)) =
    ε.app (B.obj (P, Q)) ≫ tPQ ≫ aPQ.hom at hmPQ
  change F.map bQN.hom ≫ μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N) ≫
      X.closed.tensor.map (Prod.mkHom (ε.app Q) (ε.app N)) =
    ε.app (B.obj (Q, N)) ≫ tQN ≫ aQN.hom at hmQN
  change F.map bL.hom ≫ μ.hom.app (DerivedCategory.Q.obj PQ, DerivedCategory.Q.obj N) ≫
      X.closed.tensor.map (Prod.mkHom (ε.app PQ) (ε.app N)) =
    ε.app (B.obj (PQ, N)) ≫ tL ≫ aL₀.hom at hmL
  change F.map bR.hom ≫ μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj QN) ≫
      X.closed.tensor.map (Prod.mkHom (ε.app P) (ε.app QN)) =
    ε.app (B.obj (P, QN)) ≫ tR ≫ aR₀.hom at hmR
  have hnL := X.coherence.tensorIso_naturality (V.obj PQ) (V.obj N)
    (A.obj (V.obj P, V.obj Q)) (V.obj N) (Or.inl hUPQ) (Or.inl hAPQ)
    ((chain P Q).hom) (𝟙 (V.obj N))
  rw [X.coherence.tensorIso_both _ _ hUPQ hUN, X.coherence.tensorIso_both _ _ hAPQ hUN] at hnL
  have hnR := X.coherence.tensorIso_naturality (V.obj P) (V.obj QN)
    (V.obj P) (A.obj (V.obj Q, V.obj N)) (Or.inl hUP) (Or.inl hUP)
    (𝟙 (V.obj P)) ((chain Q N).hom)
  rw [X.coherence.tensorIso_both _ _ hUP hUQN, X.coherence.tensorIso_both _ _ hUP hAQN] at hnR
  simp only [CoefficientClosedStructure.tensor, tensor_map,
    DerivedCategory.Q.map_id] at hnL
  erw [tensorHom_id] at hnL
  simp only [CoefficientClosedStructure.tensor, tensor_map,
    DerivedCategory.Q.map_id] at hnR
  erw [id_tensorHom] at hnR
  have hL₀ := RingedForgetTensorTransposition.left_square F μ bPQ.hom bL.hom
    (ε.app P) (ε.app Q) (ε.app N) (ε.app PQ)
    (ε.app (B.obj (PQ, N))) (tPQ ≫ aPQ.hom) (tL ≫ aL₀.hom) hmPQ hmL
  have hR₀ := RingedForgetTensorTransposition.right_square F μ bQN.hom bR.hom
    (ε.app P) (ε.app Q) (ε.app N) (ε.app QN)
    (ε.app (B.obj (P, QN))) (tQN ≫ aQN.hom) (tR ≫ aR₀.hom) hmQN hmR
  have hL : F.map lB.hom ≫
      μ.hom.app (Y.closed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q),
        DerivedCategory.Q.obj N) ≫
      (μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ▷
        F.obj (DerivedCategory.Q.obj N)) ≫
      (((ε.app P) ⊗ₘ (ε.app Q)) ⊗ₘ (ε.app N)) = eL ≫ lA.hom := by
    calc
      _ = ε.app (B.obj (PQ, N)) ≫ (tL ≫ aL₀.hom) ≫
          ((tPQ ≫ aPQ.hom) ▷ DerivedCategory.Q.obj (V.obj N)) := hL₀
      _ = _ := by
        simp only [comp_whiskerRight, Category.assoc]
        erw [← reassoc_of% hnL]
        simp only [eL, lA, Iso.trans_hom, whiskerRightIso_hom, Category.assoc]
        rfl
  have hR : F.map rB.hom ≫
      μ.hom.app (DerivedCategory.Q.obj P,
        Y.closed.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N)) ≫
      (F.obj (DerivedCategory.Q.obj P) ◁
        μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N)) ≫
      ((ε.app P) ⊗ₘ ((ε.app Q) ⊗ₘ (ε.app N))) = eR ≫ rA.hom := by
    calc
      _ = ε.app (B.obj (P, QN)) ≫ (tR ≫ aR₀.hom) ≫
          (DerivedCategory.Q.obj (V.obj P) ◁ (tQN ≫ aQN.hom)) := hR₀
      _ = _ := by
        simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
        erw [← reassoc_of% hnR]
        simp only [eR, rA, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc]
        rfl
  have hC : F.map (DerivedCategory.Q.map aB.hom) ≫ eR =
      eL ≫ DerivedCategory.Q.map aA.hom := by
    have hf := ε.naturality aB.hom
    change F.map (DerivedCategory.Q.map aB.hom) ≫
        ε.app (B.obj (P, QN)) = ε.app (B.obj (PQ, N)) ≫
          DerivedCategory.Q.map (V.map aB.hom) at hf
    dsimp only [eL, eR]
    rw [reassoc_of% hf]
    simpa only [tL, tR, A, coefficient_map_tensor X,
      tensorHom_id, id_tensorHom, Functor.map_comp, Category.assoc] using
      congrArg (fun f ↦ ε.app (B.obj (PQ, N)) ≫ DerivedCategory.Q.map f) hc
  exact RingedForgetTensorTransposition.associativity_transport F μ lB rB
    (DerivedCategory.Q.map aB.hom) lA.hom rA.hom (DerivedCategory.Q.map aA.hom)
    (asIso (ε.app P)) (asIso (ε.app Q)) (asIso (ε.app N))
    eL eR hB hA hL hR hC


set_option maxHeartbeats 800000 in
-- Normalize the dependent ringed-site representative comparison equations.
private theorem edge_unit_eq
    (j : e.pullback.obj (SheafOfModules.unit Y.ring) ≅ SheafOfModules.unit X.ring)
    (hj : ∀ M : Y.modules,
      (e.ordinaryTensor.mu M (SheafOfModules.unit Y.ring)).hom ≫
          (SheafOfModules.monoidalCategory X.A).tensorHom (𝟙 _) j.hom ≫
          ((SheafOfModules.monoidalCategory X.A).rightUnitor (e.pullback.obj M)).hom =
        e.pullback.map ((SheafOfModules.monoidalCategory Y.A).rightUnitor M).hom) :
    canonicalDerivedUnitComparison e j =
      e.left.map Y.coherence.unitIso.hom ≫
        (edgeAlpha e).app (ringedTensorUnitComplex.{u, u, u} Y.J Y.A) ≫
        DerivedCategory.Q.map (CochainPullback.unit (edgePullback.{u, w} (X := X) (Y := Y) e)
          (edgeComparison e)).hom ≫
        X.coherence.unitIso.inv := by
  dsimp only [Site.corner] at *
  have heq : j = CochainPullback.moduleUnit (edgePullback.{u, w} (X := X) (Y := Y) e)
    (edgeComparison e) := by
    exact (Classical.choose_spec
      (SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_unit
        Y.A X.A e.inverseRing e.inverse e.algebraic e.ringMap e.pullback
        e.object_eq e.map_eq (edgeComparison e))).2 j hj
  subst j
  rfl

private theorem edge_unit_iso :
    IsIso ((edgeAlpha e).app (ringedTensorUnitComplex.{u, u, u} Y.J Y.A)) := by
  dsimp only [Site.corner] at *
  exact edgeAlpha_iso e _ ((FiniteDerivedTensorModels.resolving_native Y _).1
    ⟨RingedForgetTensorTransposition.unit_kflat.{u, u, u} Y.J Y.A,
      RingedForgetTensorTransposition.unit_flat.{u, u, u} Y.J Y.A⟩)

set_option maxHeartbeats 1200000 in
-- Normalize the dependent ringed-site representative comparison equations.
include hY hX in
private theorem edge_right_unit (P : CochainComplex Y.modules ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (fP : ∀ n : ℤ, IsFlatOnSite (J := Y.J) (R := Y.A) (P.X n)) :
    (e.tensorComparison rY rX).hom.app
        (DerivedCategory.Q.obj P, Y.closed.monoidal.tensorUnit) ≫
      X.closed.tensor.map (Prod.mkHom (𝟙 _) (e.left.map Y.coherence.unitIso.hom ≫
        (edgeAlpha e).app (ringedTensorUnitComplex.{u, u, u} Y.J Y.A) ≫
        DerivedCategory.Q.map (CochainPullback.unit (edgePullback.{u, w} (X := X) (Y := Y) e)
          (edgeComparison e)).hom ≫
        X.coherence.unitIso.inv)) ≫
      (X.closed.monoidal.rightUnitor (e.left.obj (DerivedCategory.Q.obj P))).hom =
        e.left.map (Y.closed.monoidal.rightUnitor (DerivedCategory.Q.obj P)).hom := by
  dsimp only [Site.corner] at *
  let F : Y.D ⥤ X.D := e.left
  let : MonoidalCategory Y.D := Y.closed.monoidal
  let : MonoidalCategory X.D := X.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} Y.corner.mateModules) := Y.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} X.corner.mateModules) := X.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} Y.modules) := Y.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} X.modules) := X.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} (CochainPullback.Modules.{u, u, u} Y.A)) :=
    Y.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} (CochainPullback.Modules.{u, u, u} X.A)) :=
    X.closed.monoidal
  let := e.additive
  let V : CochainComplex Y.modules ℤ ⥤ CochainComplex X.modules ℤ :=
    e.pullback.mapHomologicalComplex (.up ℤ)
  let O := ringedTensorUnitComplex.{u, u, u} Y.J Y.A
  let O' := ringedTensorUnitComplex.{u, u, u} X.J X.A
  let PO := (coefficientTotalTensor.{u, u, u} Y.J Y.A).obj (P, O)
  let PO₀ := (coefficientTotalTensor.{u, u, u} X.J X.A).obj (V.obj P, V.obj O)
  let PO' := (coefficientTotalTensor.{u, u, u} X.J X.A).obj (V.obj P, O')
  let μ : Y.closed.tensor ⋙ F ≅ F.prod F ⋙ X.closed.tensor :=
    e.tensorComparison rY rX
  let ε : DerivedCategory.Q.{w} ⋙ F ⟶ V ⋙ DerivedCategory.Q.{w} := edgeAlpha e
  let c : V.obj O ≅ O' := CochainPullback.unit (edgePullback e) (edgeComparison e)
  let t : V.obj PO ≅ PO₀ :=
    CochainPullback.comparison (edgePullback e) (edgeComparison e) P O
  let k : PO₀ ≅ PO' := whiskerLeftIso (V.obj P) c
  let b : PO ⟶ P := (ρ_ P).hom
  let b' : PO' ⟶ V.obj P := (ρ_ (V.obj P)).hom
  change μ.hom.app
        (DerivedCategory.Q.obj P, Y.closed.monoidal.tensorUnit) ≫
      X.closed.tensor.map (Prod.mkHom (𝟙 _) (F.map Y.coherence.unitIso.hom ≫
        ε.app (ringedTensorUnitComplex.{u, u, u} Y.J Y.A) ≫
        DerivedCategory.Q.map (CochainPullback.unit (edgePullback.{u, w} (X := X) (Y := Y) e)
          (edgeComparison e)).hom ≫
        X.coherence.unitIso.inv)) ≫
      (X.closed.monoidal.rightUnitor (F.obj (DerivedCategory.Q.obj P))).hom =
        F.map (Y.closed.monoidal.rightUnitor (DerivedCategory.Q.obj P)).hom
  have hO := RingedForgetTensorTransposition.unit_kflat.{u, u, u} Y.J Y.A
  have fO := RingedForgetTensorTransposition.unit_flat.{u, u, u} Y.J Y.A
  have hO' := RingedForgetTensorTransposition.unit_kflat.{u, u, u} X.J X.A
  have hVP : (V.obj P).IsKFlatIndependentCoefficients := (edge_resolving e rY rX hY hX P hP fP).1
  have hVO : (V.obj O).IsKFlatIndependentCoefficients := (edge_resolving e rY rX hY hX O hO fO).1
  have := edge_alpha_isIso e P hP fP
  have := edge_unit_iso e
  have hT := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    Y.A P O hP hO fP fO
  have ht : Y.corner.mateFlat (P ⊗ O) := by
    apply (FiniteDerivedTensorModels.resolving_native Y _).1
    exact ⟨hT.1, hT.2.1⟩
  have : IsIso (ε.app PO) := edgeAlpha_iso e PO (by exact ht)
  let i := Y.model.iso Y.J Y.A Y.closed P O hP hO
  let i' := X.model.iso X.J X.A X.closed (V.obj P) O' hVP hO'
  let aP := asIso (ε.app P)
  let aO := asIso (ε.app O) ≪≫ DerivedCategory.Q.mapIso c
  let d := asIso (ε.app PO) ≪≫ DerivedCategory.Q.mapIso t ≪≫ DerivedCategory.Q.mapIso k
  have hm := edge_square e rY rX hY hX P O hP hO fP fO hVP hVO
  change F.map i.hom ≫ μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj O) ≫
      X.closed.tensor.map (Prod.mkHom (ε.app P) (ε.app O)) =
    ε.app PO ≫
      DerivedCategory.Q.map t.hom ≫
      (X.model.iso X.J X.A X.closed (V.obj P) (V.obj O) hVP hVO).hom at hm
  have hn := X.coherence.tensorIso_naturality (V.obj P) (V.obj O) (V.obj P) O'
    (Or.inl hVP) (Or.inl hVP) (𝟙 _) c.hom
  rw [X.coherence.tensorIso_both (V.obj P) (V.obj O) hVP hVO,
    X.coherence.tensorIso_both (V.obj P) O' hVP hO'] at hn
  have hk : (coefficientTotalTensor.{u, u, u} X.J X.A).map
      (X := (V.obj P, V.obj O)) (Y := (V.obj P, O')) (𝟙 (V.obj P), c.hom) =
      k.hom := by
    exact coefficient_map_tensor X (𝟙 (V.obj P)) c.hom
  rw [hk] at hn
  have hm' : F.map i.hom ≫ μ.hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj O) ≫
      X.closed.tensor.map (Prod.mkHom aP.hom aO.hom) = d.hom ≫ i'.hom := by
    dsimp only [aP, aO, d, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
      whiskerLeftIso_hom]
    have hh := congrArg (fun z ↦ z ≫ X.closed.tensor.map
      (Prod.mkHom (𝟙 (DerivedCategory.Q.obj (V.obj P))) (DerivedCategory.Q.map c.hom))) hm
    simp only [Category.assoc, ← X.closed.tensor.map_comp, Prod.mkHom, prod_comp] at hh
    simp only [DerivedCategory.Q.map_id] at hn
    erw [← hn] at hh
    have hid : ε.app P ≫ 𝟙 (DerivedCategory.Q.obj (V.obj P)) = ε.app P :=
      Category.comp_id _
    rw [hid] at hh
    simpa only [Category.assoc, Prod.mkHom] using hh
  have hb := RingedKFlatModel.rightUnitor_model_native Y.J Y.A Y.closed Y.model
    Y.symmetry Y.coherence P hP
  rw [Y.coherence.tensorIso_both P O hP hO] at hb
  have hb' := RingedKFlatModel.rightUnitor_model_native X.J X.A X.closed X.model
    X.symmetry X.coherence (V.obj P) hVP
  rw [X.coherence.tensorIso_both (V.obj P) O' hVP hO'] at hb'
  have hc : F.map (DerivedCategory.Q.map b) ≫ aP.hom =
      d.hom ≫ DerivedCategory.Q.map b' := by
    have hh := ε.naturality b
    change F.map (DerivedCategory.Q.map b) ≫ ε.app P =
      ε.app PO ≫ DerivedCategory.Q.map (V.map b) at hh
    dsimp only [aP, asIso_hom]
    rw [hh]
    have hchain : V.map b = t.hom ≫ k.hom ≫ b' :=
      (CochainPullback.cochainPullbackTensorCoherence.{u, u, u, u, u, u, u}
        (edgePullback e) (edgeComparison e)).1.2.2.2.2 P
    simpa only [d, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc] using
      congrArg (fun z ↦ ε.app PO ≫ DerivedCategory.Q.map z) hchain
  simpa only [aO, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    asIso_hom, Category.assoc, Prod.mkHom] using
    RingedForgetTensorTransposition.right_unit_of_models Y.closed X.closed F
    μ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj O)
    (DerivedCategory.Q.obj PO) (DerivedCategory.Q.obj (V.obj P))
    (DerivedCategory.Q.obj O') (DerivedCategory.Q.obj PO')
    i i' aP aO d Y.coherence.unitIso X.coherence.unitIso
    (DerivedCategory.Q.map b) (DerivedCategory.Q.map b')
    hm' hb hb' hc


set_option maxHeartbeats 1000000 in
-- Normalize the dependent ringed-site representative comparison equations.
include hY hX in
private theorem edge_symmetry (P Q : CochainComplex Y.modules ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (fP : ∀ n : ℤ, IsFlatOnSite (J := Y.J) (R := Y.A) (P.X n))
    (hQ : Q.IsKFlatIndependentCoefficients)
    (fQ : ∀ n : ℤ, IsFlatOnSite (J := Y.J) (R := Y.A) (Q.X n)) :
    e.left.map (Y.symmetry.toBraidedCategory.braiding
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
      (e.tensorComparison rY rX).hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) =
    (e.tensorComparison rY rX).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (X.symmetry.toBraidedCategory.braiding
        (e.left.obj (DerivedCategory.Q.obj P)) (e.left.obj (DerivedCategory.Q.obj Q))).hom := by
  dsimp only [Site.corner] at *
  let F : Y.D ⥤ X.D := e.left
  let : MonoidalCategory Y.D := Y.closed.monoidal
  let : MonoidalCategory X.D := X.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} Y.corner.mateModules) := Y.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} X.corner.mateModules) := X.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} Y.modules) := Y.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} X.modules) := X.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} (CochainPullback.Modules.{u, u, u} Y.A)) :=
    Y.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} (CochainPullback.Modules.{u, u, u} X.A)) :=
    X.closed.monoidal
  let := e.additive
  let V : CochainComplex Y.modules ℤ ⥤ CochainComplex X.modules ℤ :=
    e.pullback.mapHomologicalComplex (.up ℤ)
  let ε : DerivedCategory.Q.{w} ⋙ F ⟶ V ⋙ DerivedCategory.Q.{w} := edgeAlpha e
  let μ : Y.closed.tensor ⋙ F ≅ F.prod F ⋙ X.closed.tensor :=
    e.tensorComparison rY rX
  change F.map (Y.symmetry.toBraidedCategory.braiding
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
      μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) =
    μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (X.symmetry.toBraidedCategory.braiding
        (F.obj (DerivedCategory.Q.obj P)) (F.obj (DerivedCategory.Q.obj Q))).hom
  let B := coefficientTotalTensor.{u, u, u} Y.J Y.A
  let A := coefficientTotalTensor.{u, u, u} X.J X.A
  let chain : ∀ P Q : CochainComplex Y.modules ℤ,
      V.obj (B.obj (P, Q)) ≅ A.obj (V.obj P, V.obj Q) :=
    fun P Q ↦ CochainPullback.comparison (edgePullback e) (edgeComparison e) P Q
  have hVP : (V.obj P).IsKFlatIndependentCoefficients := (edge_resolving e rY rX hY hX P hP fP).1
  have hVQ : (V.obj Q).IsKFlatIndependentCoefficients := (edge_resolving e rY rX hY hX Q hQ fQ).1
  obtain ⟨sB, hsB, heB⟩ := Y.coherence.symmetry_model P Q hP hQ
  obtain ⟨sA, hsA, heA⟩ := X.coherence.symmetry_model (V.obj P) (V.obj Q) hVP hVQ
  let σB : B.obj (P, Q) ≅ B.obj (Q, P) := CochainComplex.Monoidal.braiding P Q
  let σA : A.obj (V.obj P, V.obj Q) ≅ A.obj (V.obj Q, V.obj P) :=
    CochainComplex.Monoidal.braiding (V.obj P) (V.obj Q)
  have hbB : sB.hom = σB.hom := by
    apply CategoryTheory.tensorGenerator_ext.{u, u, u} Y.J Y.A
    intro p q n hpq U x y
    exact (hsB p q n hpq ((add_comm q p).trans hpq) U x y).trans
      ((RingedDerivedNative.complexConstraints.{u, u, u} Y.J Y.A).symmetry
        P Q p q n hpq ((add_comm q p).trans hpq) U x y).symm
  have hbA : sA.hom = σA.hom := by
    apply CategoryTheory.tensorGenerator_ext.{u, u, u} X.J X.A
    intro p q n hpq U x y
    exact (hsA p q n hpq ((add_comm q p).trans hpq) U x y).trans
      ((RingedDerivedNative.complexConstraints.{u, u, u} X.J X.A).symmetry
        (V.obj P) (V.obj Q) p q n hpq ((add_comm q p).trans hpq) U x y).symm
  have hc : V.map σB.hom ≫ (chain Q P).hom = (chain P Q).hom ≫ σA.hom :=
    (CochainPullback.cochainPullbackTensorCoherence.{u, u, u, u, u, u, u}
      (edgePullback e) (edgeComparison e)).1.2.2.1 P Q
  erw [← hbB, ← hbA] at hc
  have hm := edge_square e rY rX hY hX P Q hP hQ fP fQ hVP hVQ
  have hm' := edge_square e rY rX hY hX Q P hQ hP fQ fP hVQ hVP
  change F.map (Y.model.iso Y.J Y.A Y.closed P Q hP hQ).hom ≫
      μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      X.closed.tensor.map (Prod.mkHom (ε.app P) (ε.app Q)) =
    ε.app ((coefficientTotalTensor.{u, u, u} Y.J Y.A).obj (P, Q)) ≫
      DerivedCategory.Q.map (chain P Q).hom ≫
      (X.model.iso X.J X.A X.closed (V.obj P) (V.obj Q) hVP hVQ).hom at hm
  change F.map (Y.model.iso Y.J Y.A Y.closed Q P hQ hP).hom ≫
      μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≫
      X.closed.tensor.map (Prod.mkHom (ε.app Q) (ε.app P)) =
    ε.app ((coefficientTotalTensor.{u, u, u} Y.J Y.A).obj (Q, P)) ≫
      DerivedCategory.Q.map (chain Q P).hom ≫
      (X.model.iso X.J X.A X.closed (V.obj Q) (V.obj P) hVQ hVP).hom at hm'
  have := edge_alpha_isIso e P hP fP
  have := edge_alpha_isIso e Q hQ fQ
  let : SymmetricCategory X.D := X.symmetry
  apply (cancel_epi (F.map (Y.model.iso Y.J Y.A Y.closed P Q hP hQ).hom)).mp
  apply (cancel_mono ((ε.app Q) ⊗ₘ (ε.app P))).mp
  have hf := ε.naturality sB.hom
  change F.map (DerivedCategory.Q.map sB.hom) ≫ ε.app _ =
    ε.app _ ≫ DerivedCategory.Q.map (V.map sB.hom) at hf
  calc
    _ = F.map (DerivedCategory.Q.map sB.hom) ≫
        F.map (Y.model.iso Y.J Y.A Y.closed Q P hQ hP).hom ≫
        μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≫
        X.closed.tensor.map (Prod.mkHom (ε.app Q) (ε.app P)) := by
      erw [← F.map_comp_assoc, heB, Functor.map_comp]
      simp only [CoefficientClosedStructure.tensor, tensor_map, Category.assoc]
    _ = ε.app _ ≫ DerivedCategory.Q.map (V.map sB.hom) ≫
        DerivedCategory.Q.map (chain Q P).hom ≫
        (X.model.iso X.J X.A X.closed (V.obj Q) (V.obj P) hVQ hVP).hom := by
      erw [hm', reassoc_of% hf]
    _ = ε.app _ ≫ DerivedCategory.Q.map (chain P Q).hom ≫
        DerivedCategory.Q.map sA.hom ≫
        (X.model.iso X.J X.A X.closed (V.obj Q) (V.obj P) hVQ hVP).hom := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun z ↦ ε.app (B.obj (P, Q)) ≫ DerivedCategory.Q.map z ≫
          (X.model.iso X.J X.A X.closed (V.obj Q) (V.obj P) hVQ hVP).hom) hc
    _ = ε.app _ ≫ DerivedCategory.Q.map (chain P Q).hom ≫
        (X.model.iso X.J X.A X.closed (V.obj P) (V.obj Q) hVP hVQ).hom ≫
        (X.symmetry.toBraidedCategory.braiding
          (DerivedCategory.Q.obj (V.obj P)) (DerivedCategory.Q.obj (V.obj Q))).hom := by
      erw [← heA]
    _ = _ := by
      simp only [Category.assoc]
      erw [← BraidedCategory.braiding_naturality]
      simpa only [B, Functor.comp_obj, CoefficientClosedStructure.tensor,
        tensor_map, Category.assoc] using
        congrArg (fun z ↦ z ≫ (X.symmetry.toBraidedCategory.braiding
          (DerivedCategory.Q.obj (V.obj P)) (DerivedCategory.Q.obj (V.obj Q))).hom) hm.symm


end Representatives

set_option maxHeartbeats 800000 in
-- Normalize the dependent ringed-site representative comparison equations.
/-- Localizing the cochain coherence equations gives the diagrams for the explicit
canonical tensor and scalar-action unit maps.
Source: Stacks Project, Cohomology on Sites, Tag 07A4 and the signed model of 0FPT;
Modules on Sites, Tag 03EL.
(blueprint: lem-sfb-ringed-derived-tensor-diagrams).

Proof:
1. Use simultaneous flat-term K-flat representatives. Their tensors and pullbacks
remain in that class. The representative characterization of tensorComparison
identifies its components with the localized ordinary cochain comparisons.
2. The degree-zero coefficient complex is flat-term K-flat. Its derived pullback
comparison is therefore invertible. The given j is an ordinary unit isomorphism,
and the single-complex comparison and the site's recorded unit identifications
are isomorphisms. Their composite a is invertible.
3. On three representatives compare the two associativity routes after each
homogeneous pure-tensor summand inclusion. The recorded associators are ordinary
reassociation; the cochain pullback coherence theorem gives equality on each
such summand. Tensor extensionality and the direct-sum universal property give
the chain-map equality. Substitute the recorded tensor-model equations and
localize it to obtain the displayed associativity equation.
4. For the right unitor, the cochain equation on a degree-zero coefficient
and a homogeneous section is scalar multiplication. The normalization of j
identifies it with the cochain unit comparison. The recorded right unitor and
unitIso identify its localization with the derived right-unit equation.
5. The two symmetry routes send a tensor in degrees p,q to its swapped tensor
with sign (-1)^(p*q), by the cochain signed-braiding equation and the recorded
signed braiding models. Thus their localized maps agree. Finally every derived
object is isomorphic to a flat-term K-flat representative. Naturality conjugates
the diagram equalities to arbitrary objects. Braiding naturality and the
right-unit equation imply the left-unit equation. Cancelling the target unitors
gives the two displayed inverse-unitor equations. No exactness of the ordinary
pullback and no boundedness assumption is used. -/
theorem canonicalTensorDiagrams {X Y : Site.{u, w}}
    (e : RingedTensorEdge Y.corner X.corner)
    (rY : RingedTensorModel Y.corner) (rX : RingedTensorModel X.corner)
    (hY : ∀ P Q hP hQ,
      rY.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
        (Y.model.iso Y.J Y.A Y.closed P Q hP.1 hQ.1).hom)
    (hX : ∀ P Q hP hQ,
      rX.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
        (X.model.iso X.J X.A X.closed P Q hP.1 hQ.1).hom)
    (j : e.pullback.obj (SheafOfModules.unit Y.ring) ≅ SheafOfModules.unit X.ring)
    (hj : ∀ M : Y.modules,
      (e.ordinaryTensor.mu M (SheafOfModules.unit Y.ring)).hom ≫
          (SheafOfModules.monoidalCategory X.A).tensorHom (𝟙 _) j.hom ≫
          ((SheafOfModules.monoidalCategory X.A).rightUnitor (e.pullback.obj M)).hom =
        e.pullback.map ((SheafOfModules.monoidalCategory Y.A).rightUnitor M).hom) :
    CanonicalTensorDiagrams e rY rX j := by
  dsimp only [Site.corner] at *
  let F : Y.D ⥤ X.D := e.left
  let : MonoidalCategory Y.D := Y.closed.monoidal
  let : MonoidalCategory X.D := X.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} Y.corner.mateModules) := Y.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} X.corner.mateModules) := X.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} Y.modules) := Y.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} X.modules) := X.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} (CochainPullback.Modules.{u, u, u} Y.A)) :=
    Y.closed.monoidal
  let : MonoidalCategory (DerivedCategory.{w} (CochainPullback.Modules.{u, u, u} X.A)) :=
    X.closed.monoidal
  let : SymmetricCategory Y.D := Y.symmetry
  let : SymmetricCategory X.D := X.symmetry
  let μ : Y.closed.tensor ⋙ F ≅ F.prod F ⋙ X.closed.tensor :=
    e.tensorComparison rY rX
  let a : F.obj (𝟙_ Y.D) ⟶ 𝟙_ X.D := canonicalDerivedUnitComparison e j
  have ha : IsIso a := by
    dsimp only [a]
    rw [edge_unit_eq e j hj]
    have := edge_unit_iso e
    infer_instance
  let η := asIso a
  have hα (U V W : Y.D) :
      F.map (α_ U V W).hom ≫ μ.hom.app (U, V ⊗ W) ≫
        F.obj U ◁ μ.hom.app (V, W) =
      μ.hom.app (U ⊗ V, W) ≫ μ.hom.app (U, V) ▷ F.obj W ≫
        (α_ (F.obj U) (F.obj V) (F.obj W)).hom := by
    obtain ⟨P, hP, fP, ⟨iP⟩⟩ := RingedForgetTensorTransposition.flat_representative.{u, u, u, w}
      Y.J Y.A U
    obtain ⟨Q, hQ, fQ, ⟨iQ⟩⟩ := RingedForgetTensorTransposition.flat_representative.{u, u, u, w}
      Y.J Y.A V
    obtain ⟨N, hN, fN, ⟨iN⟩⟩ := RingedForgetTensorTransposition.flat_representative.{u, u, u, w}
      Y.J Y.A W
    have hh := edge_associativity e rY rX hY hX P Q N hP fP hQ fQ hN fN
    change F.map (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj N)).hom ≫
        μ.hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj N) ≫
        F.obj (DerivedCategory.Q.obj P) ◁
          μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N) =
      μ.hom.app
          (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N) ≫
        μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ▷
          F.obj (DerivedCategory.Q.obj N) ≫
        (α_ (F.obj (DerivedCategory.Q.obj P)) (F.obj (DerivedCategory.Q.obj Q))
          (F.obj (DerivedCategory.Q.obj N))).hom at hh
    simpa only [Functor.comp_obj, Functor.prod_obj, tensor_obj,
      Iso.app_hom, RingedForgetTensorTransposition.rho,
      CoefficientClosedStructure.tensor,
      tensor_map, tensorHom_id, id_tensorHom] using
      RingedForgetTensorTransposition.associator_of_iso Y.closed X.closed F μ
        iP iQ iN (by
          simpa only [Functor.comp_obj, Functor.prod_obj, tensor_obj,
            Iso.app_hom, RingedForgetTensorTransposition.rho,
            CoefficientClosedStructure.tensor, tensor_map, id_tensorHom, tensorHom_id] using hh)
  have hβ (U V : Y.D) :
      F.map (β_ U V).hom ≫ μ.hom.app (V, U) =
        μ.hom.app (U, V) ≫ (β_ (F.obj U) (F.obj V)).hom := by
    obtain ⟨P, hP, fP, ⟨iP⟩⟩ := RingedForgetTensorTransposition.flat_representative.{u, u, u, w}
      Y.J Y.A U
    obtain ⟨Q, hQ, fQ, ⟨iQ⟩⟩ := RingedForgetTensorTransposition.flat_representative.{u, u, u, w}
      Y.J Y.A V
    exact RingedForgetTensorTransposition.symmetry_of_iso Y.closed X.closed F μ
      Y.symmetry X.symmetry iP iQ (edge_symmetry e rY rX hY hX P Q hP fP hQ fQ)
  have hr (U : Y.D) :
      μ.hom.app (U, 𝟙_ Y.D) ≫ F.obj U ◁ a ≫ (ρ_ (F.obj U)).hom =
        F.map (ρ_ U).hom := by
    obtain ⟨P, hP, fP, ⟨iP⟩⟩ := RingedForgetTensorTransposition.flat_representative.{u, u, u, w}
      Y.J Y.A U
    have hh := edge_right_unit e rY rX hY hX P hP fP
    rw [← edge_unit_eq e j hj] at hh
    simpa only [CoefficientClosedStructure.tensor, tensor_map, id_tensorHom,
      η, asIso_hom] using
      RingedForgetTensorTransposition.right_unit_of_iso Y.closed X.closed F μ η iP hh
  have hl (U : Y.D) :
      μ.hom.app (𝟙_ Y.D, U) ≫ a ▷ F.obj U ≫ (λ_ (F.obj U)).hom =
        F.map (λ_ U).hom := by
    exact left_from_right (B := Y.D) (A := X.D) F
      (fun U V ↦ μ.hom.app (U, V)) a hβ hr U
  change IsIso a ∧ _
  refine ⟨ha, fun U V W ↦ (hα U V W).symm, ?_, ?_, fun U V ↦ (hβ U V).symm⟩
  · intro U
    change (λ_ (F.obj U)).inv =
      F.map (λ_ U).inv ≫ μ.hom.app (𝟙_ Y.D, U) ≫ a ▷ F.obj U
    apply (cancel_mono (λ_ (F.obj U)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id]
    rw [hl, ← F.map_comp, Iso.inv_hom_id, F.map_id]
  · intro U
    change (ρ_ (F.obj U)).inv =
      F.map (ρ_ U).inv ≫ μ.hom.app (U, 𝟙_ Y.D) ≫ F.obj U ◁ a
    apply (cancel_mono (ρ_ (F.obj U)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id]
    rw [hr, ← F.map_comp, Iso.inv_hom_id, F.map_id]

end CategoryTheory.RingedDerivedComparisons
