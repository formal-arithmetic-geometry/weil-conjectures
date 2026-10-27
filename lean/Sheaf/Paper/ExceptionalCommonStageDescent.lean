/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q111
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.PbcScalarExtension
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.CategoryTheory.StageSystemFunctorDescent
import Sheaf.Paper.PbcVerdierAxioms
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # Exceptional scalar comparisons and common-stage descent

Source: main-20261015, prop-sf-localization-all-stages.proof.md,
algebraically closed stage (blueprint: lem-sf-exceptional-common-stage-descent).

The records package the input and output clauses on the actual raw rational
categories. Scalar functors and associators are the recorded coefficient system.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u v c h
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

namespace WeilConjectures
namespace ExceptionalCommonStage

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X Z U : Scheme.{u})

/-- The signed shift equation for the connecting arrow of a support triangle.
This names the displayed equation to avoid unfolding the concrete coefficient
categories during its elaboration. It uses the existing functor shift structures.
Source: localization proof, algebraically closed stage, step 6
(blueprint: lem-sf-exceptional-common-stage-descent). -/
def boundaryShiftCompatible
    {C : Type c} [Category.{h} C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    (A B : C ⥤ C) [A.CommShift ℤ] [B.CommShift ℤ]
    (δ : ∀ K : C, A.obj K ⟶ (B.obj K)⟦(1 : ℤ)⟧) : Prop :=
  ∀ (K : C) (n : ℤ),
    δ (K⟦n⟧) ≫ (shiftFunctor C (1 : ℤ)).map ((B.commShiftIso n).hom.app K) =
      (A.commShiftIso n).hom.app K ≫ (n.negOnePow • (shiftFunctor C n).map (δ K)) ≫
        (shiftFunctorComm C (1 : ℤ) n).hom.app (B.obj K)

/-- The stipulated exact finite-stage adjunctions and their actual support arrows.
Source: localization proof, algebraically closed stage, input paragraph
(blueprint: lem-sf-exceptional-common-stage-descent). -/
structure FiniteData where
  closedPull : (stageSystem l Ω X).Morphism (stageSystem l Ω Z)
  closedPush : (stageSystem l Ω Z).Morphism (stageSystem l Ω X)
  openPull : (stageSystem l Ω X).Morphism (stageSystem l Ω U)
  openPush : (stageSystem l Ω U).Morphism (stageSystem l Ω X)
  exceptional : ∀ E : Index l Ω, Stage l Ω X E ⥤ Stage l Ω Z E
  closedAdj : ∀ E, closedPull.Φ E ⊣ closedPush.Φ E
  openAdj : ∀ E, openPull.Φ E ⊣ openPush.Φ E
  exceptionalAdj : ∀ E, closedPush.Φ E ⊣ exceptional E
  closedPullShift : ∀ E, (closedPull.Φ E).CommShift ℤ
  closedPushShift : ∀ E, (closedPush.Φ E).CommShift ℤ
  openPullShift : ∀ E, (openPull.Φ E).CommShift ℤ
  openPushShift : ∀ E, (openPush.Φ E).CommShift ℤ
  exceptionalShift : ∀ E, (exceptional E).CommShift ℤ
  boundary : ∀ E (K : Stage l Ω X E),
    (openPush.Φ E).obj ((openPull.Φ E).obj K) ⟶
      ((closedPush.Φ E).obj ((exceptional E).obj K))⟦(1 : ℤ)⟧

attribute [instance] FiniteData.closedPullShift FiniteData.closedPushShift
  FiniteData.openPullShift FiniteData.openPushShift FiniteData.exceptionalShift

variable {l Ω X Z U}


/-- The actual scalar unitor after the recorded stage-transition identification.
Source: localization proof, algebraically closed stage, identity coefficient inclusions
(blueprint: lem-sf-exceptional-common-stage-descent). -/
def scalarUnit (Y : Scheme.{u}) (E : Index l Ω) :
    (stageSystem l Ω Y).T (le_refl E) ≅ 𝟭 (Stage l Ω Y E) :=
  operationStageTransitionIso l Ω Y E E (le_refl E) ≪≫ unitor l Ω Y E

/-- Exactness, canonical adjunction shifts, orthogonality, and the projection mates.
The coherence of the four input comparisons is the existing Morphism.coh equation.
Source: localization proof, algebraically closed stage, hypotheses and step 1
(blueprint: lem-sf-exceptional-common-stage-descent). -/
structure Hypotheses (D : FiniteData l Ω X Z U) : Prop where
  closedPullExact : ∀ E, (D.closedPull.Φ E).IsTriangulated
  closedPushExact : ∀ E, (D.closedPush.Φ E).IsTriangulated
  openPullExact : ∀ E, (D.openPull.Φ E).IsTriangulated
  openPushExact : ∀ E, (D.openPush.Φ E).IsTriangulated
  exceptionalExact : ∀ E, (D.exceptional E).IsTriangulated
  closedShift : ∀ E, (D.closedAdj E).CommShift ℤ
  openShift : ∀ E, (D.openAdj E).CommShift ℤ
  exceptionalShift : ∀ E, (D.exceptionalAdj E).CommShift ℤ
  closedCounit : ∀ E, IsIso (D.closedAdj E).counit
  openCounit : ∀ E, IsIso (D.openAdj E).counit
  orthogonal : ∀ E (P : Stage l Ω Z E) (N : Stage l Ω U E) (n : ℤ),
    Subsingleton (((D.closedPush.Φ E).obj P)⟦n⟧ ⟶ (D.openPush.Φ E).obj N)
  distinguished : ∀ E (K : Stage l Ω X E),
    Triangle.mk ((D.exceptionalAdj E).counit.app K)
      ((D.openAdj E).unit.app K) (D.boundary E K) ∈ distTriang (Stage l Ω X E)
  inputShift : ∀ (E L : Index l Ω) (h : E ≤ L),
    NatTrans.CommShift (D.closedPull.β h).hom ℤ ∧
    NatTrans.CommShift (D.closedPush.β h).hom ℤ ∧
    NatTrans.CommShift (D.openPull.β h).hom ℤ ∧
    NatTrans.CommShift (D.openPush.β h).hom ℤ
  inputUnit : ∀ (E : Index l Ω),
    (∀ K, (D.closedPull.β (le_refl E)).hom.app K ≫
      (D.closedPull.Φ E).map ((scalarUnit X E).hom.app K) =
        (scalarUnit Z E).hom.app ((D.closedPull.Φ E).obj K)) ∧
    (∀ K, (D.closedPush.β (le_refl E)).hom.app K ≫
      (D.closedPush.Φ E).map ((scalarUnit Z E).hom.app K) =
        (scalarUnit X E).hom.app ((D.closedPush.Φ E).obj K)) ∧
    (∀ K, (D.openPull.β (le_refl E)).hom.app K ≫
      (D.openPull.Φ E).map ((scalarUnit X E).hom.app K) =
        (scalarUnit U E).hom.app ((D.openPull.Φ E).obj K)) ∧
    (∀ K, (D.openPush.β (le_refl E)).hom.app K ≫
      (D.openPush.Φ E).map ((scalarUnit U E).hom.app K) =
        (scalarUnit X E).hom.app ((D.openPush.Φ E).obj K))
  closedMate : ∀ (E L : Index l Ω) (h : E ≤ L),
    (mateEquiv (D.closedAdj E) (D.closedAdj L)
      (TwoSquare.mk _ _ _ _ (D.closedPull.β h).inv)).natTrans = (D.closedPush.β h).hom
  openMate : ∀ (E L : Index l Ω) (h : E ≤ L),
    (mateEquiv (D.openAdj E) (D.openAdj L)
      (TwoSquare.mk _ _ _ _ (D.openPull.β h).inv)).natTrans = (D.openPush.β h).hom


/-- Pin the left adjoints and their coefficient maps to the recorded geometric
pullbacks. Invertibility witnesses are quantified, not assumed: they are images
of the base-field unit under the canonical residue maps. Right adjoints are the
specified adjunctions in FiniteData; their comparisons are fixed by the mate laws.
Source: localization proof, algebraically closed stage, canonical input comparisons
(blueprint: lem-sf-exceptional-common-stage-descent). -/
structure GeometricNormalization (i : Z ⟶ X) (j : U ⟶ X)
    (D : FiniteData l Ω X Z U) : Prop where
  closedPull : ∀ (E : Index l Ω)
    [_a : ∀ z : Z, Invertible (l : Z.residueField z)]
    [_b : ∀ x : X, Invertible (l : X.residueField x)],
    D.closedPull.Φ E = rationalDerivedPullback l (Coefficient.{u} l Ω E) i
  openPull : ∀ (E : Index l Ω)
    [_a : ∀ t : U, Invertible (l : U.residueField t)]
    [_b : ∀ x : X, Invertible (l : X.residueField x)],
    D.openPull.Φ E = rationalDerivedPullback l (Coefficient.{u} l Ω E) j
  closedComparison : ∀ (E L : Index l Ω) (h : E ≤ L)
    [_a : ∀ z : Z, Invertible (l : Z.residueField z)]
    [_b : ∀ x : X, Invertible (l : X.residueField x)] (K : Stage l Ω X E),
    HEq ((D.closedPull.β h).app K) (commonStagePullbackComparison l Ω i ⟨E, K⟩ L h)
  openComparison : ∀ (E L : Index l Ω) (h : E ≤ L)
    [_a : ∀ t : U, Invertible (l : U.residueField t)]
    [_b : ∀ x : X, Invertible (l : X.residueField x)] (K : Stage l Ω X E),
    HEq ((D.openPull.β h).app K) (commonStagePullbackComparison l Ω j ⟨E, K⟩ L h)


/-- The actual mate transformation; invertibility is a conclusion, never an assumption.
Source: localization proof, algebraically closed stage, step 4
(blueprint: lem-sf-exceptional-common-stage-descent). -/
def comparison (D : FiniteData l Ω X Z U) {E L : Index l Ω} (h : E ≤ L) :
    D.exceptional E ⋙ (stageSystem l Ω Z).T h ⟶
      (stageSystem l Ω X).T h ⋙ D.exceptional L :=
  (mateEquiv (D.exceptionalAdj E) (D.exceptionalAdj L)
    (TwoSquare.mk _ _ _ _ (D.closedPush.β h).inv)).natTrans

/-- The closed comparison and exceptional mate on the first support vertex.
Source: localization proof, algebraically closed stage, steps 3--4
(blueprint: lem-sf-exceptional-common-stage-descent). -/
def firstMap (D : FiniteData l Ω X Z U) {E L : Index l Ω} (h : E ≤ L)
    (K : Stage l Ω X E) :=
  (D.closedPush.β h).hom.app ((D.exceptional E).obj K) ≫
    (D.closedPush.Φ L).map ((comparison D h).app K)

/-- The open comparison with its pullback identification on the last support vertex.
Source: localization proof, algebraically closed stage, step 1
(blueprint: lem-sf-exceptional-common-stage-descent). -/
def lastMap (D : FiniteData l Ω X Z U) {E L : Index l Ω} (h : E ≤ L)
    (K : Stage l Ω X E) :=
  (D.openPush.β h).hom.app ((D.openPull.Φ E).obj K) ≫
    (D.openPush.Φ L).map ((D.openPull.β h).hom.app K)

/-- The finite-stage conclusions, including uniqueness and all three triangle squares.
Source: localization proof, algebraically closed stage, steps 1--6
(blueprint: lem-sf-exceptional-common-stage-descent). -/
structure FiniteConclusion (D : FiniteData l Ω X Z U) : Prop where
  invertible : ∀ (E L : Index l Ω) (h : E ≤ L), IsIso (comparison D h)
  unique : ∀ (E L : Index l Ω) (h : E ≤ L)
      (b : D.exceptional E ⋙ (stageSystem l Ω Z).T h ⟶
        (stageSystem l Ω X).T h ⋙ D.exceptional L),
    (∀ K, (D.closedPush.Φ L).map (b.app K) ≫
      (D.exceptionalAdj L).counit.app (((stageSystem l Ω X).T h).obj K) =
        (D.closedPush.β h).inv.app ((D.exceptional E).obj K) ≫
          ((stageSystem l Ω X).T h).map ((D.exceptionalAdj E).counit.app K)) →
      b = comparison D h
  counit : ∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
    firstMap D h K ≫
        (D.exceptionalAdj L).counit.app (((stageSystem l Ω X).T h).obj K) =
      ((stageSystem l Ω X).T h).map ((D.exceptionalAdj E).counit.app K)
  unit : ∀ (E L : Index l Ω) (h : E ≤ L) (P : Stage l Ω Z E),
    ((stageSystem l Ω Z).T h).map ((D.exceptionalAdj E).unit.app P) ≫
        (comparison D h).app ((D.closedPush.Φ E).obj P) =
      (D.exceptionalAdj L).unit.app (((stageSystem l Ω Z).T h).obj P) ≫
        (D.exceptional L).map ((D.closedPush.β h).inv.app P)
  identity : ∀ (E : Index l Ω) (K : Stage l Ω X E),
    (comparison D (le_refl E)).app K ≫
        (D.exceptional E).map ((scalarUnit X E).hom.app K) =
      (scalarUnit Z E).hom.app ((D.exceptional E).obj K)
  tower : ∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) (K : Stage l Ω X E),
    ((stageSystem l Ω Z).T k).map ((comparison D h).app K) ≫
        (comparison D k).app (((stageSystem l Ω X).T h).obj K) ≫
        (D.exceptional M).map (((stageSystem l Ω X).assoc h k).hom.app K) =
      ((stageSystem l Ω Z).assoc h k).hom.app ((D.exceptional E).obj K) ≫
        (comparison D (h.trans k)).app K
  shift : ∀ (E L : Index l Ω) (h : E ≤ L), NatTrans.CommShift (comparison D h) ℤ
  openUnit : ∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
    ((stageSystem l Ω X).T h).map ((D.openAdj E).unit.app K) ≫ lastMap D h K =
      (D.openAdj L).unit.app (((stageSystem l Ω X).T h).obj K)
  third : ∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
    ((stageSystem l Ω X).T h).map (D.boundary E K) ≫
        (((stageSystem l Ω X).T h).commShiftIso (1 : ℤ)).hom.app
          ((D.closedPush.Φ E).obj ((D.exceptional E).obj K)) ≫
        (shiftFunctor (Stage l Ω X L) (1 : ℤ)).map (firstMap D h K) =
      lastMap D h K ≫ D.boundary L (((stageSystem l Ω X).T h).obj K)

  boundaryNatural : ∀ (E : Index l Ω) (K K' : Stage l Ω X E) (f : K ⟶ K'),
    (D.openPull.Φ E ⋙ D.openPush.Φ E).map f ≫ D.boundary E K' =
      D.boundary E K ≫ (shiftFunctor (Stage l Ω X E) (1 : ℤ)).map
        ((D.exceptional E ⋙ D.closedPush.Φ E).map f)
  boundaryShift : ∀ E : Index l Ω,
    boundaryShiftCompatible (D.openPull.Φ E ⋙ D.openPush.Φ E)
      (D.exceptional E ⋙ D.closedPush.Φ E) (D.boundary E)


/-- Assemble the coherent exceptional system using the specified mate and its inverse.
The only choices are inverses to isomorphisms, uniquely determined by their maps.
Source: localization proof, algebraically closed stage, steps 5--7
(blueprint: lem-sf-exceptional-common-stage-descent). -/
def exceptionalSystem (D : FiniteData l Ω X Z U) (F : FiniteConclusion D) :
    (stageSystem l Ω X).Morphism (stageSystem l Ω Z) where
  Φ := D.exceptional
  β := fun {E L} h ↦ @asIso _ _ _ _ (comparison D h) (F.invertible E L h)
  coh := fun {E L M} h k K ↦ F.tower E L M h k K

/-- Descent on the same pair categories with the actual units, counits and all arrows.
Every Hom is the existing directed-colimit Hom group; the formula below prescribes
its action on every representative, including representatives with different stages.
Source: localization proof, algebraically closed stage, steps 7--9
(blueprint: lem-sf-exceptional-common-stage-descent). -/
structure Descent (D : FiniteData l Ω X Z U) (F : FiniteConclusion D) where
  [closedPullShift : D.closedPull.functor.CommShift ℤ]
  [closedPushShift : D.closedPush.functor.CommShift ℤ]
  [openPullShift : D.openPull.functor.CommShift ℤ]
  [openPushShift : D.openPush.functor.CommShift ℤ]
  closedPullExact : D.closedPull.functor.IsTriangulated
  closedPushExact : D.closedPush.functor.IsTriangulated
  openPullExact : D.openPull.functor.IsTriangulated
  openPushExact : D.openPush.functor.IsTriangulated
  inputShiftNormalization : ∀ E : Index l Ω,
    NatTrans.CommShift (D.closedPull.ιCompFunctorIso E).hom ℤ ∧
    NatTrans.CommShift (D.closedPush.ιCompFunctorIso E).hom ℤ ∧
    NatTrans.CommShift (D.openPull.ιCompFunctorIso E).hom ℤ ∧
    NatTrans.CommShift (D.openPush.ιCompFunctorIso E).hom ℤ
  exceptionalShift : (exceptionalSystem D F).functor.CommShift ℤ
  exceptionalExact :
    (fun [_s : (exceptionalSystem D F).functor.CommShift ℤ] ↦
      (exceptionalSystem D F).functor.IsTriangulated) (_s := exceptionalShift)
  exceptionalAdditive : (exceptionalSystem D F).functor.Additive
  shiftNormalization :
    (fun [_s : (exceptionalSystem D F).functor.CommShift ℤ] ↦
      ∀ (E : Index l Ω) (K : Stage l Ω X E) (n : ℤ),
        HEq ((((exceptionalSystem D F).functor).commShiftIso n).hom.app ⟨E, K⟩)
          ((inclusion E : Stage l Ω Z E ⥤ Pair l Ω Z).map
            (((D.exceptional E).commShiftIso n).hom.app K))) (_s := exceptionalShift)
  representative : ∀ (P Q : Pair l Ω X) (M : Index l Ω)
      (hP : P.stage ≤ M) (hQ : Q.stage ≤ M) (f : P.toStage hP ⟶ Q.toStage hQ),
    (exceptionalSystem D F).functor.map (StageSystem.PairCategory.mkHom M hP hQ f) =
      StageSystem.PairCategory.mkHom
        (X := (exceptionalSystem D F).functor.obj P)
        (Y := (exceptionalSystem D F).functor.obj Q) M hP hQ
        (((exceptionalSystem D F).β hP).hom.app P.obj ≫
          (D.exceptional M).map f ≫ ((exceptionalSystem D F).β hQ).inv.app Q.obj)
  closedAdj : D.closedPull.functor ⊣ D.closedPush.functor
  openAdj : D.openPull.functor ⊣ D.openPush.functor
  exceptionalAdj : D.closedPush.functor ⊣ (exceptionalSystem D F).functor
  closedShift : closedAdj.CommShift ℤ
  openShift : openAdj.CommShift ℤ
  adjunctionShift :
    (fun [_s : (exceptionalSystem D F).functor.CommShift ℤ] ↦
      exceptionalAdj.CommShift ℤ) (_s := exceptionalShift)
  closedUnit : ∀ (E : Index l Ω) (K : Stage l Ω X E),
    HEq (closedAdj.unit.app ⟨E, K⟩)
      ((inclusion E : Stage l Ω X E ⥤ Pair l Ω X).map ((D.closedAdj E).unit.app K))
  closedCounit : ∀ (E : Index l Ω) (P : Stage l Ω Z E),
    HEq (closedAdj.counit.app ⟨E, P⟩)
      ((inclusion E : Stage l Ω Z E ⥤ Pair l Ω Z).map ((D.closedAdj E).counit.app P))
  openUnit : ∀ (E : Index l Ω) (K : Stage l Ω X E),
    HEq (openAdj.unit.app ⟨E, K⟩)
      ((inclusion E : Stage l Ω X E ⥤ Pair l Ω X).map ((D.openAdj E).unit.app K))
  openCounit : ∀ (E : Index l Ω) (N : Stage l Ω U E),
    HEq (openAdj.counit.app ⟨E, N⟩)
      ((inclusion E : Stage l Ω U E ⥤ Pair l Ω U).map ((D.openAdj E).counit.app N))
  exceptionalUnit : ∀ (E : Index l Ω) (P : Stage l Ω Z E),
    HEq (exceptionalAdj.unit.app ⟨E, P⟩)
      ((inclusion E : Stage l Ω Z E ⥤ Pair l Ω Z).map
        ((D.exceptionalAdj E).unit.app P))
  exceptionalCounit : ∀ (E : Index l Ω) (K : Stage l Ω X E),
    HEq (exceptionalAdj.counit.app ⟨E, K⟩)
      ((inclusion E : Stage l Ω X E ⥤ Pair l Ω X).map
        ((D.exceptionalAdj E).counit.app K))
  boundary : D.openPull.functor ⋙ D.openPush.functor ⟶
    (exceptionalSystem D F).functor ⋙ D.closedPush.functor ⋙
      shiftFunctor (Pair l Ω X) (1 : ℤ)
  boundaryNormalization : ∀ (E : Index l Ω) (K : Stage l Ω X E),
    HEq (boundary.app ⟨E, K⟩)
      ((inclusion E : Stage l Ω X E ⥤ Pair l Ω X).map (D.boundary E K) ≫
        ((inclusion E : Stage l Ω X E ⥤ Pair l Ω X).commShiftIso (1 : ℤ)).hom.app
          ((D.closedPush.Φ E).obj ((D.exceptional E).obj K)))
  distinguished : ∀ K : Pair l Ω X,
    Triangle.mk (exceptionalAdj.counit.app K) (openAdj.unit.app K)
      (boundary.app K) ∈ distTriang (Pair l Ω X)
  orthogonal : ∀ (P : Pair l Ω Z) (N : Pair l Ω U) (n : ℤ),
    Subsingleton ((D.closedPush.functor.obj P)⟦n⟧ ⟶ D.openPush.functor.obj N)


/-- The signed shift compatibility of the descended boundary, using precisely the
shift structures in the descent data. Kept separate from the dependent data record.
Source: localization proof, algebraically closed stage, steps 6--9
(blueprint: lem-sf-exceptional-common-stage-descent). -/
def Descent.boundaryShift (D : FiniteData l Ω X Z U) (F : FiniteConclusion D)
    (R : Descent D F) : Prop :=
  (fun [_a : D.openPull.functor.CommShift ℤ]
      [_b : D.openPush.functor.CommShift ℤ]
      [_c : (exceptionalSystem D F).functor.CommShift ℤ]
      [_d : D.closedPush.functor.CommShift ℤ] ↦
    boundaryShiftCompatible (D.openPull.functor ⋙ D.openPush.functor)
      ((exceptionalSystem D F).functor ⋙ D.closedPush.functor) R.boundary.app)
    (_a := R.openPullShift) (_b := R.openPushShift)
    (_c := R.exceptionalShift) (_d := R.closedPushShift)

/-- Counit-normalized exceptional comparison and descent, on the actual rational
and algebraically closed coefficient categories.
Source: main-20261015 prop-sf-localization-all-stages.proof.md, algebraically closed
stage (blueprint: lem-sf-exceptional-common-stage-descent).

Proof plan (the nine steps of the node).
1. Apply unit_mateEquiv to the open projection mate: lastMap sends the extended
open unit to the specified open unit, using lem-pur-mate-unit-compatibility.
2. The closed counit makes closedPush fully faithful. Exact scalar extension
carries the given support triangle to a distinguished triangle. The four input
comparisons identify its open and closed vertices with those at the larger field.
3. Hom-into-triangle exactness and orthogonality in shifts zero and minus one
make postcomposition with the target exceptional counit bijective. Lift the first
arrow uniquely. TR3 completes the map of triangles. Hom-out-of-triangle exactness
and shifted orthogonality force its third component to be lastMap. The triangle
isomorphism lemma then makes the first component invertible; full faithfulness
lifts it to the exceptional comparison and its inverse.
4. Its counit equation identifies it with comparison, the actual mate of the
inverse closed comparison. The mate bijection gives uniqueness and its unit
equation, by lem-amb-mate-unit-counit and lem-pur-mate-unit-compatibility.
5. Mate pasting gives the tower equation with the actual scalar associators and
the identity equation with scalarUnit. Apply the same calculation to shifts.
The canonical adjunction-compatible right shifts are unique, by
lem-weil-pbc-adjunction-shift-compatibility-unique, so comparison commutes with them.
6. The two Hom-exactness arguments force every component of a support-triangle
map from its middle component. Backward rotation gives uniqueness of its boundary.
Consequently all three arrows commute with coefficient identities, towers and
shifts, as well as with maps of K.
7. Apply lem-sbc-coherent-pair-functor-descent to exceptionalSystem. Conjugation by
its comparisons gives exactly representative. The tower equation makes this
independent of common field and representatives; cancellation gives composition.
Descend the compatible adjunction maps and boundary in the same way.
8. The finite adjunction bijections pass to the directed Hom colimits: their
formulas use the compatible exceptional unit and counit. Their composites are
identities at a common stage, and their naturality is checked there too. Apply
lem-weil-pbc-adjunction-of-natural-bijection; transposing identity maps gives the
stated stagewise units and counits. The closed and open adjunctions descend by
the identical construction with their specified mates.
9. Every distinguished triangle is represented at a finite field. Exactness of
the inclusion, supplied by def-weil-algebraically-closed-coefficients and
thm-weil-pbc-verdier-axioms, proves descended distinguishedness and exactness.
Every cross-stage closed-to-open morphism is represented after enlargement by a
map in a zero finite-stage Hom group, so every such class is zero. -/
theorem exceptionalCommonStageDescent
    {l : ℕ} [Fact l.Prime]
    {Ω : Type v} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    {X Z U : Scheme.{u}} (s : X ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))
    [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (D : FiniteData l Ω X Z U) (hD : Hypotheses D)
    (hgeom : GeometricNormalization i j D) :
    ∃ (F : FiniteConclusion D) (R : Descent D F), R.boundaryShift D F := by
  sorry

end ExceptionalCommonStage
end WeilConjectures
