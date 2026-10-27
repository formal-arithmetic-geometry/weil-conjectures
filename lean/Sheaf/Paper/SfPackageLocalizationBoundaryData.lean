/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum

/-! # Canonical localization arrows and coefficient boundary predicates

These are the unchanged definitions used by the package localization realization.
They are exposed separately so coefficient transport can be proved independently.
(blueprint: def-sf-package-localization-boundary-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.longLine false
set_option linter.tacticAnalysis false
set_option linter.style.multiGoal false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w a b v' w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] sfRationalTriangulationDatum sfIntegralConstructible
  ScalarLocalization.composition

section Arrows
variable {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type v}
  [∀ X, Category.{w} (B X)] (P : SixFunctorPushStage D B)
  {Z U X Y : SixFunctorSpace D} (i : Z ⟶ X) (j : U ⟶ X) (f : X ⟶ Y)
  (hj : IsOpenImmersion j.hom.left) [IsProper i.hom.left]
  (c : Compactification f.hom.left)
  (cj : Compactification (j ≫ f).hom.left) (ci : Compactification (i ≫ f).hom.left)

/-- Identify the actual open compact-support value with the image of j!j*.
Source: package clause (3), composition and identity-proper open identification
(blueprint: lem-sf-package-localization-projection-realization). -/
def sfPackageLocalizationOpenComparison :
    P.pull j ⋙ P.support (j ≫ f) cj ≅
      (P.pull j ⋙ P.openExtension j hj) ⋙ P.support f c :=
  Functor.isoWhiskerLeft (P.pull j)
      (P.composition j f (sixFunctorOpenCompactification j hj) c cj ≪≫
        Functor.isoWhiskerRight (P.openIdentification j hj) (P.support f c)) ≪≫
    (Functor.associator _ _ _).symm

/-- Identify the actual closed compact-support value with the image of Ri*i*.
Source: package clause (3), composition and proper coincidence
(blueprint: lem-sf-package-localization-projection-realization). -/
def sfPackageLocalizationClosedComparison :
    P.pull i ⋙ P.support (i ≫ f) ci ≅ (P.pull i ⋙ P.direct i) ⋙ P.support f c :=
  Functor.isoWhiskerLeft (P.pull i)
      (P.composition i f (.ofIsProper i.hom.left) c ci ≪≫
        Functor.isoWhiskerRight (P.properIdentity i) (P.support f c)) ≪≫
    (Functor.associator _ _ _).symm

/-- The first arrow is exactly the image of the open counit, after composition.
Source: package clause (3)
(blueprint: lem-sf-package-localization-projection-realization). -/
def sfPackageLocalizationFirst :
    P.pull j ⋙ P.support (j ≫ f) cj ⟶ P.support f c :=
  (sfPackageLocalizationOpenComparison P j f hj c cj).hom ≫
    Functor.whiskerRight (P.openAdjunction j hj).counit (P.support f c) ≫
    (Functor.leftUnitor (P.support f c)).hom

/-- The second arrow is exactly the image of the closed unit, after proper coincidence.
Source: package clause (3)
(blueprint: lem-sf-package-localization-projection-realization). -/
def sfPackageLocalizationSecond :
    P.support f c ⟶ P.pull i ⋙ P.support (i ≫ f) ci :=
  (Functor.leftUnitor (P.support f c)).inv ≫
    Functor.whiskerRight (P.pullDirectAdjunction i).unit (P.support f c) ≫
    (sfPackageLocalizationClosedComparison P i f c ci).inv

variable {A : Type a} [Category.{b} A] [HasShift A ℤ]
  (V : B Y ⥤ A)

/-- A natural boundary on the actual three functor values; it is not a choice of
three unrelated vertex isomorphisms. Source: package clause (3)
(blueprint: lem-sf-package-localization-projection-realization). -/
def SfPackageLocalizationBoundary :=
  (P.pull i ⋙ P.support (i ≫ f) ci) ⋙ V ⟶
    ((P.pull j ⋙ P.support (j ≫ f) cj) ⋙ V) ⋙ shiftFunctor A (1 : ℤ)

/-- The displayed triangle, with its specified first two arrows.
Source: package clause (3)
(blueprint: lem-sf-package-localization-projection-realization). -/
def sfPackageLocalizationTriangle
    (δ : SfPackageLocalizationBoundary P i j f cj ci V) (K : B X) : Triangle A :=
  Triangle.mk (V.map ((sfPackageLocalizationFirst P j f hj c cj).app K))
    (V.map ((sfPackageLocalizationSecond P i f c ci).app K)) (δ.app K)

variable {M : Type a} [Category.{b} M] [HasShift M ℤ]

/-- Equality of the boundary with the image of the prescribed recollement boundary.
The two outer identifications are the canonical composition/proper/open comparisons.
The middle comparison identifies the actual support functor with its realization.
Source: package clause (3), conjugation by (a,1,b)
(blueprint: lem-sf-package-localization-projection-realization). -/
def SfPackageLocalizationRealizes
    [Preadditive M] [HasZeroObject M]
    [∀ m : ℤ, (shiftFunctor M m).Additive] [Pretriangulated M]
    (I : B X ⥤ M) (F : M ⥤ A) (sF : F.CommShift ℤ)
    (comparison : P.support f c ⋙ V ≅ I ⋙ F)
    (δ : SfPackageLocalizationBoundary P i j f cj ci V)
    (Q : ObjectProperty (B X)) : Prop :=
  ∀ (K : B X), Q K →
    (∃ d : I.obj ((P.pull i ⋙ P.direct i).obj K) ⟶
        (I.obj ((P.pull j ⋙ P.openExtension j hj).obj K))⟦(1 : ℤ)⟧,
      Triangle.mk (I.map ((P.openAdjunction j hj).counit.app K))
        (I.map ((P.pullDirectAdjunction i).unit.app K)) d ∈ distTriang M) ∧
    ∀ d : I.obj ((P.pull i ⋙ P.direct i).obj K) ⟶
        (I.obj ((P.pull j ⋙ P.openExtension j hj).obj K))⟦(1 : ℤ)⟧,
      Triangle.mk (I.map ((P.openAdjunction j hj).counit.app K))
        (I.map ((P.pullDirectAdjunction i).unit.app K)) d ∈ distTriang M →
      δ.app K = V.map ((sfPackageLocalizationClosedComparison P i f c ci).hom.app K) ≫
        comparison.hom.app ((P.pull i ⋙ P.direct i).obj K) ≫ F.map d ≫
        (Functor.commShiftIso F (self := sF) (1 : ℤ)).hom.app
          (I.obj ((P.pull j ⋙ P.openExtension j hj).obj K)) ≫
        (shiftFunctor A (1 : ℤ)).map
          (comparison.inv.app ((P.pull j ⋙ P.openExtension j hj).obj K)) ≫
        (shiftFunctor A (1 : ℤ)).map
          (V.map ((sfPackageLocalizationOpenComparison P j f hj c cj).inv.app K))

variable [Preadditive A] [HasZeroObject A]
  [∀ m : ℤ, (shiftFunctor A m).Additive] [Pretriangulated A]

/-- Functorial distinguished localization on the specified input domain.
Source: package clause (3); no nonemptiness assumption on either stratum
(blueprint: lem-sf-package-localization-projection-realization). -/
def SfPackageLocalizationConclusion (Q : ObjectProperty (B X)) : Prop :=
  ∃ δ : SfPackageLocalizationBoundary P i j f cj ci V,
    ∀ K : B X, Q K → sfPackageLocalizationTriangle P i j f hj c cj ci V δ K ∈ distTriang A

end Arrows

section CoefficientMaps
variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
  {P : SixFunctorPushStage D B} {P' : SixFunctorPushStage D B'}
  {L : ∀ X, B X ⥤ B' X} (a : SixFunctorCoefficientComparison P P' L)
  {V X Y : SixFunctorSpace D} (g : V ⟶ X) (f : X ⟶ Y)
  (cg : Compactification (g ≫ f).hom.left)

/-- The coefficient comparison on an actual outer vertex is pullback comparison
followed by compact-support comparison. Source: package clause (3), field passage
(blueprint: lem-sf-package-localization-projection-realization). -/
def sfPackageLocalizationCoefficientVertex (K : B X) :
    (L Y).obj ((P.support (g ≫ f) cg).obj ((P.pull g).obj K)) ≅
      (P'.support (g ≫ f) cg).obj ((P'.pull g).obj ((L X).obj K)) :=
  ((a.supportAdjunction (g ≫ f) cg).left.app ((P.pull g).obj K)) ≪≫
    (P'.support (g ≫ f) cg).mapIso ((a.directAdjunction g).left.app K)

variable {Z U : SixFunctorSpace D} (i : Z ⟶ X) (j : U ⟶ X)
  (cj : Compactification (j ≫ f).hom.left) (ci : Compactification (i ≫ f).hom.left)
  [HasShift (B Y) ℤ] [HasShift (B' Y) ℤ]

/-- Coefficient change preserves the connecting arrow, with its actual outer
comparisons and its shift. Naturality supplies the first two squares from the
unit/counit equations already in a. Source: package clause (3), field passage
(blueprint: lem-sf-package-localization-projection-realization). -/
def SfPackageLocalizationCoefficientBoundary (s : (L Y).CommShift ℤ)
    (δ : SfPackageLocalizationBoundary P i j f cj ci (𝟭 (B Y)))
    (δ' : SfPackageLocalizationBoundary P' i j f cj ci (𝟭 (B' Y))) : Prop :=
  ∀ K : B X,
    (L Y).map (δ.app K) ≫
        (Functor.commShiftIso (L Y) (self := s) (1 : ℤ)).hom.app
          ((P.support (j ≫ f) cj).obj ((P.pull j).obj K)) ≫
        (shiftFunctor (B' Y) (1 : ℤ)).map
          (sfPackageLocalizationCoefficientVertex a j f cj K).hom =
      (sfPackageLocalizationCoefficientVertex a i f ci K).hom ≫ δ'.app ((L X).obj K)
end CoefficientMaps







section BoundarySystem
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
  {Z U X Y : SixFunctorSpace D} (i : Z ⟶ X) (j : U ⟶ X) (f : X ⟶ Y)
  [IsProper i.hom.left] (hj : IsOpenImmersion j.hom.left)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  (c : Compactification f.hom.left)
  (cj : Compactification (j ≫ f).hom.left) (ci : Compactification (i ≫ f).hom.left)

/-- A boundary is pinned to the one strict-tower image, including its normalized
projections, map action and composite shift. Its ambient arrow is the image of
this very boundary under the fully faithful inclusion and its prescribed shift.
Source: package clause (3), coherent integral realization
(blueprint: lem-sf-package-localization-projection-realization). -/
def SfPackageLocalizationTowerBoundary (H : SixFunctorHigherOperations D C E)
    (hl : IsUnit (C.l : D.k))
    (δI : SfPackageLocalizationBoundary H.integral i j f cj ci
      (𝟭 (sfIntegralConstructibleCategory C.l E Y.obj.left))) : Prop :=
    (fun [_products : HasCountableProducts
        (DerivedCategory (scalarReductionSource C.l E Y.obj.left))] ↦
      ∃ T : CompactSupportReductionTowerConstruction C.l E f.hom.left c,
      T.tower = Classical.choose (Classical.choose_spec (Classical.choose_spec
        (exists_compactSupportReductionTower C.l E D.k X.obj.left Y.obj.left
          f.hom.left hl c))).2.2 ∧
      ∃ (sT : T.tower.CommShift ℤ) (sL : T.limit.CommShift ℤ),
      (fun [_shiftT : T.tower.CommShift ℤ] ↦ T.tower.IsTriangulated) (_shiftT := sT) ∧
      (fun [_shiftL : T.limit.CommShift ℤ] ↦ T.limit.IsTriangulated) (_shiftL := sL) ∧
      ∃ (sF : (T.tower ⋙ T.limit).CommShift ℤ)
        (e : H.integral.support f c ⋙
          (sfIntegralConstructible C.l E Y.obj.left).ι ≅
          (sfIntegralConstructible C.l E X.obj.left).ι ⋙ (T.tower ⋙ T.limit))
        (δ : SfPackageLocalizationBoundary H.integral i j f cj ci
          (sfIntegralConstructible C.l E Y.obj.left).ι),
        (∀ (K : sfIntegralConstructibleCategory C.l E X.obj.left) (m : ℕ),
          HEq (e.hom.app K ≫ (T.projections m).app (T.tower.obj K.obj) ≫
              (T.evaluations m).hom.app K.obj)
            (Classical.choose (Classical.choose_spec (exists_isDerivedLimit_and_iso
              (sfCompactSupportTerm C.l E c K.obj)
              (sfCompactSupportTransition C.l E c K.obj)).1) ≫
                Pi.π (sfCompactSupportTerm C.l E c K.obj) m)) ∧
        (∀ K : sfIntegralConstructibleCategory C.l E X.obj.left,
          δ.app K = (sfIntegralConstructible C.l E Y.obj.left).ι.map (δI.app K) ≫
            ((sfIntegralConstructible C.l E Y.obj.left).ι.commShiftIso (1 : ℤ)).hom.app
              ((H.integral.pull j ⋙ H.integral.support (j ≫ f) cj).obj K)) ∧
        SfPackageLocalizationRealizes H.integral i j f hj c cj ci
          (sfIntegralConstructible C.l E Y.obj.left).ι
          (sfIntegralConstructible C.l E X.obj.left).ι (T.tower ⋙ T.limit) sF e δ
          (fun _ ↦ True) ∧
        (∀ K : sfIntegralConstructibleCategory C.l E X.obj.left,
          sfPackageLocalizationTriangle H.integral i j f hj c cj ci
            (sfIntegralConstructible C.l E Y.obj.left).ι δ K ∈ distTriang _) ∧
        (∀ (K L : sfIntegralConstructibleCategory C.l E X.obj.left) (v : K ⟶ L),
          (sfIntegralConstructible C.l E Y.obj.left).ι.map
              ((H.integral.support f c).map v) ≫ e.hom.app L =
            e.hom.app K ≫ T.limit.map (T.tower.map v.hom)) ∧
        ∀ K : DerivedCategory (scalarReductionSource C.l E X.obj.left),
          (Functor.commShiftIso (T.tower ⋙ T.limit) (self := sF) (1 : ℤ)).hom.app K =
            T.limit.map ((Functor.commShiftIso T.tower (self := sT) (1 : ℤ)).hom.app K) ≫
              (Functor.commShiftIso T.limit (self := sL) (1 : ℤ)).hom.app (T.tower.obj K))
      (_products := integralOperationsDerivedCountableProducts C.l E Y.obj.left)

/-- The rational boundary is the exact rationalization of the tower-pinned integral
boundary, through the datum's specified coefficient comparisons and canonical shift.
Source: package clause (3), rationalization of the coherent triangle
(blueprint: lem-sf-package-localization-projection-realization). -/
def SfPackageLocalizationRationalBoundary (H : SixFunctorHigherOperations D C E)
    (hl : IsUnit (C.l : D.k))
    (δR : SfPackageLocalizationBoundary H.rational i j f cj ci
      (𝟭 (sfRationalConstructibleCategory C.l E Y.obj.left))) : Prop :=
  ∃ δI : SfPackageLocalizationBoundary H.integral i j f cj ci
      (𝟭 (sfIntegralConstructibleCategory C.l E Y.obj.left)),
    SfPackageLocalizationTowerBoundary i j f hj c cj ci H hl δI ∧
    SfPackageLocalizationCoefficientBoundary H.rationalization f i j cj ci
      (sfRationalLocalizationCommShift C.l E Y.obj.left) δI δR ∧
    ∀ K : sfRationalConstructibleCategory C.l E X.obj.left,
      sfPackageLocalizationTriangle H.rational i j f hj c cj ci
        (𝟭 (sfRationalConstructibleCategory C.l E Y.obj.left)) δR K ∈ distTriang _

variable {n : ℕ} {hn : 1 ≤ n} (S : SixFunctorOperationDatum D C E n hn)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- One family of finite-field boundaries is used both for exact inclusions and
all scalar transitions. Every member is pinned to its integral tower; the common
boundary is its image under every prescribed exact inclusion.
Source: package clause (3), common finite coefficient stages
(blueprint: lem-sf-package-localization-projection-realization). -/
def SfPackageLocalizationFieldSystem (hl : IsUnit (C.l : D.k))
    (δR : SfPackageLocalizationBoundary S.higher.rational i j f cj ci
      (𝟭 (sfRationalConstructibleCategory C.l E Y.obj.left)))
    (δE : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      SfPackageLocalizationBoundary
        (sixFunctorCoefficientRational D C S.closure.coefficientStages E₀) i j f cj ci
        (𝟭 (GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar Y.obj.left E₀)))
    (δbar : SfPackageLocalizationBoundary S.closure.commonStage i j f cj ci
      (𝟭 (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Y.obj.left))) : Prop :=
  SfPackageLocalizationRationalBoundary i j f hj c cj ci S.higher hl δR ∧
  (∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
    SfPackageLocalizationRationalBoundary i j f hj c cj ci
      (S.closure.coefficientStages E₀) hl (δE E₀)) ∧
  (∀ K : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left,
    sfPackageLocalizationTriangle S.closure.commonStage i j f hj c cj ci
      (𝟭 (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Y.obj.left)) δbar K ∈
        distTriang _) ∧
  (∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
    SfPackageLocalizationCoefficientBoundary (S.closure.commonStageComparison E₀)
      f i j cj ci (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift
        (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀) (δE E₀) δbar) ∧
  ∀ (E₀ L : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E₀ ≤ L),
    SfPackageLocalizationCoefficientBoundary (S.closure.coefficientTransition h)
      f i j cj ci (GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift
        C.l C.Qbar Y.obj.left E₀ L h) (δE E₀) (δE L)

end BoundarySystem

end WeilConjectures
