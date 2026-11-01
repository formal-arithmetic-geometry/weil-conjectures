/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.SixFunctors.PodConstructibleMate.ConstructibleWeilModelSquares
public import WeilConjectures.SmoothPurity.Supporting.SixFunctorDatum
public import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusGeometricExchange
public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.PoincareDuality.SemilinearFieldOperationLifts
public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluation
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.SixFunctors.Normalized.NormalizedRationalEvaluationNaturality
import WeilConjectures.PoincareDuality.NormalizedCommonEvaluationNaturality

/-! # Constructible exceptional Frobenius mates and their coherence
Source: blueprint main-20261015, sec-poincare-duality/sk-lem-finite,
prop-weil-operations.proof.md, sentence 1; lem-fix-weil-operations.proof.md,
adjunction and comparison paragraphs (blueprint: lem-pod-constructible-mate-coherence).
The exceptional functor is the right adjoint on the constructible category itself.
All fixed pairs use the existing IsoAlgebra construction and its original carrier Hom sets.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v a b c d e f g h
open CategoryTheory CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures
namespace PodConstructibleMate

/-- The complete mate and lifted-adjunction assertion for the specified adjunction and
specified left comparison. This predicate introduces no new functors or comparisons.
Source: prop-weil-operations.proof.md, sentence 1, exceptional-adjunction paragraph
(blueprint: lem-pod-constructible-mate-coherence). -/
def AdjunctionCoherent
    {C : Type a} {B : Type b} [Category.{c} C] [Category.{d} B]
    (S : C ⥤ C) (T : B ⥤ B) {F : C ⥤ B} {G : B ⥤ C}
    (adj : F ⊣ G) (α : F ⋙ T ≅ S ⋙ F) : Prop :=
  IsIso (mateEquiv adj adj α.inv).natTrans ∧
  ∃ β : G ⋙ S ≅ T ⋙ G,
    β.hom = (mateEquiv adj adj α.inv).natTrans ∧
    (∀ L : B, β.hom.app L =
      adj.unit.app (S.obj (G.obj L)) ≫ G.map (α.inv.app (G.obj L)) ≫
        G.map (T.map (adj.counit.app L))) ∧
    PodCovariantWeilLiftSpec G β ∧
    (∀ K : C, S.map (adj.unit.app K) ≫ β.hom.app (F.obj K) ≫
      G.map (α.hom.app K) = adj.unit.app (S.obj K)) ∧
    (∀ L : B, α.hom.app (G.obj L) ≫ F.map (β.hom.app L) ≫
      adj.counit.app (T.obj L) = T.map (adj.counit.app L)) ∧
    (∀ K : IsoAlgebra S,
      S.map (adj.unit.app K.carrier) ≫
        ((IsoAlgebra.mapOfNatIso β).obj ((IsoAlgebra.mapOfNatIso α).obj K)).str.hom =
      K.str.hom ≫ adj.unit.app K.carrier) ∧
    (∀ L : IsoAlgebra T,
      ((IsoAlgebra.mapOfNatIso α).obj ((IsoAlgebra.mapOfNatIso β).obj L)).str.hom ≫
        adj.counit.app L.carrier = T.map (adj.counit.app L.carrier) ≫ L.str.hom) ∧
    ∃ A : IsoAlgebra.mapOfNatIso α ⊣ IsoAlgebra.mapOfNatIso β,
      (∀ K : IsoAlgebra S, (A.unit.app K).hom.f = adj.unit.app K.carrier) ∧
      (∀ L : IsoAlgebra T, (A.counit.app L).hom.f = adj.counit.app L.carrier) ∧
      (∀ K : C, F.map (adj.unit.app K) ≫ adj.counit.app (F.obj K) = 𝟙 _) ∧
      ∀ L : B, adj.unit.app (G.obj L) ≫ G.map (adj.counit.app L) = 𝟙 _

/-- The specified rational Frobenius functor at a finite-type model.
Source: prop-weil-operations.proof.md, geometric Frobenius
(blueprint: lem-pod-constructible-mate-coherence). -/
@[irreducible] def rationalFrobenius (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [_root_.Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (X : Models D) :
    sfRationalConstructibleCategory C.l E ((fiberModels D).obj X).obj.left ⥤
      sfRationalConstructibleCategory C.l E ((fiberModels D).obj X).obj.left :=
  sfWeilFrobeniusPullback D C.l C.different X.obj E

/-- The existing category structures, named once for the operation-stage interface.
Source: prop-weil-operations.proof.md, constructible operation domains
(blueprint: lem-pod-constructible-mate-coherence). -/
abbrev rationalStageCategory (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [_root_.Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] :
    ∀ X : SixFunctorSpace D, Category.{u + 2} (sfRationalConstructibleCategory C.l E X.obj.left) :=
  fun _X ↦ inferInstance

/-- All finite-type model operations below are restrictions of this recorded stage.
This abbreviation changes no operation or comparison.
Source: prop-weil-operations.proof.md, constructible operation domains
(blueprint: lem-pod-constructible-mate-coherence). -/
abbrev RationalStage (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [_root_.Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] :=
  SixFunctorPushStage D (fun X ↦ sfRationalConstructibleCategory C.l E X.obj.left)

/-- The canonical tensor on a geometric fiber with its inherited coefficient units.
Source: prop-weil-operations.proof.md, standard tensor
(blueprint: lem-pod-constructible-mate-coherence). -/
@[irreducible] def rationalModelTensor (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [_root_.Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (X : Models D) :
    sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left ×
      sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left ⥤
        sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left :=
  letI := fun x ↦ sfWeilPrimeInvertible D C.l C.different X.obj x
  rationalDerivedTensor C.l E (D.geometricFiber X.obj).left

/-- The actual tensor Frobenius comparison, before applying the input structures.
Source: prop-weil-operations.proof.md, standard tensor
(blueprint: lem-pod-constructible-mate-coherence). -/
def rationalModelTensorComparison (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [_root_.Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (X : Models D)
    (K L : sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left) :=
  letI := fun x ↦ sfWeilPrimeInvertible D C.l C.different X.obj x
  canonicalRationalPullbackTensor C.l E (D.geometricFrobenius X.obj).hom K L

/-- The literal pullback-composition Frobenius square at a model morphism.
Source: lem-fix-weil-operations.proof.md, ordinary pullback comparison
(blueprint: lem-pod-constructible-mate-coherence). -/
def rationalModelPullbackComponent (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [_root_.Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {X Y : Models D} (f₀ : X ⟶ Y)
    (K : sfRationalConstructibleCategory C.l E (D.geometricFiber Y.obj).left) :=
  letI := fun x ↦ sfWeilPrimeInvertible D C.l C.different X.obj x
  letI := fun y ↦ sfWeilPrimeInvertible D C.l C.different Y.obj y
  podRationalSquarePullbackComponent (X := (D.geometricFiber X.obj).left)
    (Y := (D.geometricFiber Y.obj).left) C.l E (FrobeniusExchange.fiberMap D f₀.hom)
    (D.geometricFrobenius X.obj).hom (D.geometricFrobenius Y.obj).hom
    (D.frobenius_square_cartesian X.obj Y.obj f₀.hom).2.2.2.2.1 K

/-- A coherent lift uses the specified pullback square, its direct-image mate, and
literal rationalized compact-support exchange. Normalizations refer to the existing
canonical maps, rather than accepting arbitrary natural isomorphisms.
Source: prop-weil-operations.proof.md, sentence 1 and comparison paragraph
(blueprint: lem-pod-constructible-mate-coherence). -/
structure RationalLifts
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [_root_.Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (A : RationalStage D C E) where
  pull : ∀ {X Y : Models D} (f₀ : X ⟶ Y),
    (@SixFunctorPushStage.pull
      D _ (rationalStageCategory D C E) A) ((fiberModels D).map f₀) ⋙ rationalFrobenius D C E X ≅
      rationalFrobenius D C E Y ⋙ (@SixFunctorPushStage.pull
        D _ (rationalStageCategory D C E) A) ((fiberModels D).map f₀)
  pullNormalization : ∀ {X Y : Models D} (f₀ : X ⟶ Y)
    (K : sfRationalConstructibleCategory C.l E (D.geometricFiber Y.obj).left),
    HEq ((pull f₀).app K) (rationalModelPullbackComponent D C E f₀ K)
  direct : ∀ {X Y : Models D} (f₀ : X ⟶ Y),
    (@SixFunctorPushStage.direct
      D _ (rationalStageCategory D C E) A) ((fiberModels D).map f₀) ⋙ rationalFrobenius D C E Y ≅
      rationalFrobenius D C E X ⋙ (@SixFunctorPushStage.direct
        D _ (rationalStageCategory D C E) A) ((fiberModels D).map f₀)
  directMate : ∀ {X Y : Models D} (f₀ : X ⟶ Y),
    (direct f₀).hom = (mateEquiv
      ((@SixFunctorPushStage.pullDirectAdjunction
        D _ (rationalStageCategory D C E) A) ((fiberModels D).map f₀))
      ((@SixFunctorPushStage.pullDirectAdjunction
        D _ (rationalStageCategory D C E) A) ((fiberModels D).map f₀)) (pull f₀).inv).natTrans
  support : ∀ {X Y : Models D} (f₀ : X ⟶ Y)
    (_c₀ : Compactification f₀.hom.left)
    (c : Compactification ((fiberModels D).map f₀).hom.left),
    (@SixFunctorPushStage.support
      D _ (rationalStageCategory D C E) A) ((fiberModels D).map f₀) c ⋙ rationalFrobenius D C E Y ≅
      rationalFrobenius D C E X ⋙ (@SixFunctorPushStage.support
        D _ (rationalStageCategory D C E) A) ((fiberModels D).map f₀) c
  supportNormalization : ∀ {X Y : Models D} (f₀ : X ⟶ Y)
    [IsSeparated f₀.hom.left] [LocallyOfFiniteType f₀.hom.left] [QuasiCompact f₀.hom.left]
    (c₀ : Compactification f₀.hom.left)
    (K : sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left),
    HEq ((support f₀ c₀ (FrobeniusExchange.geometricCompactification D f₀.hom c₀)).hom.app K)
      ((FrobeniusExchange.frobeniusRational D C.l C.different E f₀.hom
        (FrobeniusExchange.frobeniusCompactModel D f₀.hom c₀)).app K)
  supportConjugation : ∀ {X Y : Models D} (f₀ : X ⟶ Y)
    (c₀ : Compactification f₀.hom.left)
    (c : Compactification ((fiberModels D).map f₀).hom.left),
    (support f₀ c₀ c).hom =
      Functor.whiskerRight
        ((@SixFunctorPushStage.comparison
          D _ (rationalStageCategory D C E) A) ((fiberModels D).map f₀) c
          (FrobeniusExchange.geometricCompactification D f₀.hom c₀)).hom
        (rationalFrobenius D C E Y) ≫
      (support f₀ c₀ (FrobeniusExchange.geometricCompactification D f₀.hom c₀)).hom ≫
      Functor.whiskerLeft (rationalFrobenius D C E X)
        ((@SixFunctorPushStage.comparison
          D _ (rationalStageCategory D C E) A) ((fiberModels D).map f₀)
          (FrobeniusExchange.geometricCompactification D f₀.hom c₀) c).hom
  exceptional : ∀ {X Y : Models D} (f₀ : X ⟶ Y)
    (_c₀ : Compactification f₀.hom.left)
    (c : Compactification ((fiberModels D).map f₀).hom.left),
    (@SixFunctorPushStage.exceptional
      D _ (rationalStageCategory D C E) A) ((fiberModels D).map f₀) c ⋙ rationalFrobenius D C E X ≅
      rationalFrobenius D C E Y ⋙ (@SixFunctorPushStage.exceptional
        D _ (rationalStageCategory D C E) A) ((fiberModels D).map f₀) c
  exceptionalMate : ∀ {X Y : Models D} (f₀ : X ⟶ Y)
    (c₀ : Compactification f₀.hom.left)
    (c : Compactification ((fiberModels D).map f₀).hom.left),
    (exceptional f₀ c₀ c).hom = (mateEquiv
      ((@SixFunctorPushStage.exceptionalAdjunction
        D _ (rationalStageCategory D C E) A) ((fiberModels D).map f₀) c)
      ((@SixFunctorPushStage.exceptionalAdjunction
        D _ (rationalStageCategory D C E) A) ((fiberModels D).map f₀) c)
      (support f₀ c₀ c).inv).natTrans
  tensor : ∀ X : Models D,
    rationalModelTensor D C E X ⋙ rationalFrobenius D C E X ≅
      (rationalFrobenius D C E X).prod (rationalFrobenius D C E X) ⋙
        rationalModelTensor D C E X
  tensorNormalization : ∀ (X : Models D)
    (K L : sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left),
    HEq ((tensor X).app (K, L)) (rationalModelTensorComparison D C E X K L)

/-- The specified pullback Weil functor. Source: lem-fix-weil-operations.proof.md
(blueprint: lem-pod-constructible-mate-coherence). -/
@[irreducible] def RationalLifts.pullFunctor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [_root_.Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {A : RationalStage D C E}
    (L : RationalLifts D C E A) {X Y : Models D} (f : X ⟶ Y) :
    IsoAlgebra (rationalFrobenius D C E Y) ⥤ IsoAlgebra (rationalFrobenius D C E X) :=
  IsoAlgebra.mapOfNatIso (F := rationalFrobenius D C E Y)
    (G := rationalFrobenius D C E X)
    (L := (@SixFunctorPushStage.pull
      D _ (rationalStageCategory D C E) A) ((fiberModels D).map f)) (L.pull f)

/-- The specified direct-image Weil functor. Source: lem-fix-weil-operations.proof.md
(blueprint: lem-pod-constructible-mate-coherence). -/
@[irreducible] def RationalLifts.directFunctor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [_root_.Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {A : RationalStage D C E}
    (L : RationalLifts D C E A) {X Y : Models D} (f : X ⟶ Y) :
    IsoAlgebra (rationalFrobenius D C E X) ⥤ IsoAlgebra (rationalFrobenius D C E Y) :=
  IsoAlgebra.mapOfNatIso (F := rationalFrobenius D C E X)
    (G := rationalFrobenius D C E Y)
    (L := (@SixFunctorPushStage.direct
      D _ (rationalStageCategory D C E) A) ((fiberModels D).map f)) (L.direct f)

/-- The specified compact-support Weil functor. Source: lem-fix-weil-operations.proof.md
(blueprint: lem-pod-constructible-mate-coherence). -/
@[irreducible] def RationalLifts.supportFunctor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [_root_.Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {A : RationalStage D C E}
    (L : RationalLifts D C E A) {X Y : Models D} (f : X ⟶ Y)
    (c₀ : Compactification f.hom.left)
    (c : Compactification ((fiberModels D).map f).hom.left) :
    IsoAlgebra (rationalFrobenius D C E X) ⥤ IsoAlgebra (rationalFrobenius D C E Y) :=
  IsoAlgebra.mapOfNatIso (F := rationalFrobenius D C E X)
    (G := rationalFrobenius D C E Y)
    (L := (@SixFunctorPushStage.support
      D _ (rationalStageCategory D C E) A) ((fiberModels D).map f) c)
      (L.support f c₀ c)

/-- The specified exceptional Weil functor. Source: prop-weil-operations.proof.md
(blueprint: lem-pod-constructible-mate-coherence). -/
@[irreducible] def RationalLifts.exceptionalFunctor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [_root_.Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {A : RationalStage D C E}
    (L : RationalLifts D C E A) {X Y : Models D} (f : X ⟶ Y)
    (c₀ : Compactification f.hom.left)
    (c : Compactification ((fiberModels D).map f).hom.left) :
    IsoAlgebra (rationalFrobenius D C E Y) ⥤ IsoAlgebra (rationalFrobenius D C E X) :=
  IsoAlgebra.mapOfNatIso (F := rationalFrobenius D C E Y)
    (G := rationalFrobenius D C E X)
    (L := (@SixFunctorPushStage.exceptional
      D _ (rationalStageCategory D C E) A) ((fiberModels D).map f) c) (L.exceptional f c₀ c)

/-- The specified tensor Weil bifunctor, using the existing product transport.
Source: lem-fix-weil-operations.proof.md
(blueprint: lem-pod-constructible-mate-coherence). -/
@[irreducible] def RationalLifts.tensorFunctor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [_root_.Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {A : RationalStage D C E}
    (L : RationalLifts D C E A) (X : Models D) :
    IsoAlgebra (rationalFrobenius D C E X) × IsoAlgebra (rationalFrobenius D C E X) ⥤
      IsoAlgebra (rationalFrobenius D C E X) :=
  IsoAlgebra.prod (F₁ := rationalFrobenius D C E X)
    (F₂ := rationalFrobenius D C E X) ⋙ IsoAlgebra.mapOfNatIso (L.tensor X)

/-- Every canonical comparison retains its exact carrier. An existential lifted
natural transformation is precisely a proof of its Weil equation; the carrier
conditions fix the transformation uniquely. Isomorphism outputs are used only
for the comparisons already invertible in the underlying construction.
Source: prop-weil-operations.proof.md, all comparison clauses
(blueprint: lem-pod-constructible-mate-coherence). -/
def RationalCoherence
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [_root_.Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (A : SixFunctorHigherOperations D C E)
    (L : RationalLifts D C E A.rational) : Prop :=
  -- ordinaryAdjunction
  (∀ {X Y : Models D} (f : X ⟶ Y),
    AdjunctionCoherent (rationalFrobenius D C E Y) (rationalFrobenius D C E X)
      ((@SixFunctorPushStage.pullDirectAdjunction
        D _ (rationalStageCategory D C E) A.rational) ((fiberModels D).map f)) (L.pull f)) ∧
  -- exceptionalAdjunction
  (∀ {X Y : Models D} (f : X ⟶ Y)
    (c₀ : Compactification f.hom.left)
    (c : Compactification ((fiberModels D).map f).hom.left),
    AdjunctionCoherent (rationalFrobenius D C E X) (rationalFrobenius D C E Y)
      ((@SixFunctorPushStage.exceptionalAdjunction
        D _ (rationalStageCategory D C E) A.rational) ((fiberModels D).map f) c)
      (L.support f c₀ c)) ∧
  -- pullComposition
  (∀ {X Y Z : Models D} (f : X ⟶ Y) (g : Y ⟶ Z),
    ∃ w : L.pullFunctor (f ≫ g) ≅ L.pullFunctor g ⋙ L.pullFunctor f,
      ∀ K, HEq ((w.hom.app K).hom.f)
        (((@SixFunctorPushStage.pullComposition
          D _ (rationalStageCategory D C E) A.rational) ((fiberModels D).map f)
          ((fiberModels D).map g)).hom.app K.carrier)) ∧
  -- directComposition
  (∀ {X Y Z : Models D} (f : X ⟶ Y) (g : Y ⟶ Z),
    ∃ w : L.directFunctor (f ≫ g) ≅ L.directFunctor f ⋙ L.directFunctor g,
      ∀ K, HEq ((w.hom.app K).hom.f)
        ((sixFunctorDirectComposition A.rational ((fiberModels D).map f)
          ((fiberModels D).map g)).hom.app K.carrier)) ∧
  -- supportComparison
  (∀ {X Y : Models D} (f : X ⟶ Y)
    (c₀ d₀ : Compactification f.hom.left)
    (c d : Compactification ((fiberModels D).map f).hom.left),
    ∃ w : L.supportFunctor f c₀ c ≅ L.supportFunctor f d₀ d,
      ∀ K, HEq ((w.hom.app K).hom.f)
        (((@SixFunctorPushStage.comparison
          D _ (rationalStageCategory D C E) A.rational) ((fiberModels D).map f) c d).hom.app
          K.carrier)) ∧
  -- supportComposition
  (∀ {X Y Z : Models D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf₀ : Compactification f.hom.left) (cg₀ : Compactification g.hom.left)
    (cfg₀ : Compactification (f ≫ g).hom.left)
    (cf : Compactification ((fiberModels D).map f).hom.left)
    (cg : Compactification ((fiberModels D).map g).hom.left)
    (cfg : Compactification ((fiberModels D).map (f ≫ g)).hom.left),
    ∃ w : L.supportFunctor (f ≫ g) cfg₀ cfg ≅
      L.supportFunctor f cf₀ cf ⋙ L.supportFunctor g cg₀ cg,
      ∀ K, HEq ((w.hom.app K).hom.f)
        (((@SixFunctorPushStage.composition
          D _ (rationalStageCategory D C E) A.rational)
          ((fiberModels D).map f) ((fiberModels D).map g)
          cf cg (fiberCompositionCompactification D f g cfg)).hom.app K.carrier)) ∧
  -- exceptionalComposition
  (∀ {X Y Z : Models D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf₀ : Compactification f.hom.left) (cg₀ : Compactification g.hom.left)
    (cfg₀ : Compactification (f ≫ g).hom.left)
    (cf : Compactification ((fiberModels D).map f).hom.left)
    (cg : Compactification ((fiberModels D).map g).hom.left)
    (cfg : Compactification ((fiberModels D).map (f ≫ g)).hom.left),
    ∃ w : L.exceptionalFunctor (f ≫ g) cfg₀ cfg ≅
      L.exceptionalFunctor g cg₀ cg ⋙ L.exceptionalFunctor f cf₀ cf,
      ∀ K, HEq ((w.hom.app K).hom.f)
        ((sixFunctorExceptionalComposition A.rational
          ((fiberModels D).map f) ((fiberModels D).map g)
          cf cg (fiberCompositionCompactification D f g cfg)).hom.app K.carrier)) ∧
  -- directExchange
  (∀ Q : ModelSquare D,
    ∃ w : L.directFunctor Q.f ⋙ L.pullFunctor Q.g ⟶
      L.pullFunctor Q.g' ⋙ L.directFunctor Q.f',
      (∀ K, HEq ((w.app K).hom.f)
        ((A.rationalExchange Q.fiber).stage.exchange.app K.carrier)) ∧
      (IsIso (A.rationalExchange Q.fiber).stage.exchange → IsIso w)) ∧
  -- compactExchange
  (∀ (Q : ModelSquare D)
    (c₀ : Compactification Q.f.hom.left) (c₀' : Compactification Q.f'.hom.left),
    ∃ w : L.supportFunctor Q.f c₀ Q.fiber.compactification ⋙ L.pullFunctor Q.g ⟶
      L.pullFunctor Q.g' ⋙ L.supportFunctor Q.f' c₀' Q.fiber.compactification',
      (∀ K, HEq ((w.app K).hom.f)
        ((A.rationalExchange Q.fiber).stage.compactExchange.app K.carrier)) ∧
      (IsIso (A.rationalExchange Q.fiber).stage.compactExchange → IsIso w)) ∧
  -- projection
  (∀ (Q : ModelSquare D) (c₀ : Compactification Q.f.hom.left)
    (K : IsoAlgebra (rationalFrobenius D C E Q.X))
    (N : IsoAlgebra (rationalFrobenius D C E Q.Y)),
    ∃ w : (L.tensorFunctor Q.Y).obj
        ((L.supportFunctor Q.f c₀ Q.fiber.compactification).obj K, N) ⟶
      (L.supportFunctor Q.f c₀ Q.fiber.compactification).obj
        ((L.tensorFunctor Q.X).obj (K, (L.pullFunctor Q.f).obj N)),
      HEq w.hom.f (((A.rationalExchange Q.fiber).stage.projection.app K.carrier).app N.carrier) ∧
      (IsIso (((A.rationalExchange Q.fiber).stage.projection.app K.carrier).app N.carrier) →
        IsIso w))

/-- The specified common Frobenius functor at a finite-type model.
Source: prop-weil-operations.proof.md, geometric Frobenius
(blueprint: lem-pod-constructible-mate-coherence). -/
@[irreducible] def commonFrobenius (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (X : Models D) :
    generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar ((fiberModels D).obj X).obj.left ⥤
      generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar ((fiberModels D).obj X).obj.left :=
  sfCommonStageWeilFrobeniusPullback D C.l C.different X.obj C.Qbar

/-- The existing category structures, named once for the operation-stage interface.
Source: prop-weil-operations.proof.md, constructible operation domains
(blueprint: lem-pod-constructible-mate-coherence). -/
abbrev commonStageCategory (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum) :
    ∀ X : SixFunctorSpace D,
      Category.{u + 2} (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left) :=
  fun _X ↦ inferInstance

/-- All finite-type model operations below are restrictions of this recorded stage.
This abbreviation changes no operation or comparison.
Source: prop-weil-operations.proof.md, constructible operation domains
(blueprint: lem-pod-constructible-mate-coherence). -/
abbrev CommonStage (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum) :=
  SixFunctorPushStage D
    (fun X ↦ generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)

/-- The canonical tensor on a geometric fiber with its inherited coefficient units.
Source: prop-weil-operations.proof.md, standard tensor
(blueprint: lem-pod-constructible-mate-coherence). -/
@[irreducible] def commonModelTensor (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (X : Models D) :
    generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar (D.geometricFiber X.obj).left ×
      generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar (D.geometricFiber X.obj).left ⥤
        generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar (D.geometricFiber X.obj).left :=
  letI := fun x ↦ sfWeilPrimeInvertible D C.l C.different X.obj x
  commonStageDerivedTensor C.l C.Qbar (D.geometricFiber X.obj).left

/-- The actual tensor Frobenius comparison, before applying the input structures.
Source: prop-weil-operations.proof.md, standard tensor
(blueprint: lem-pod-constructible-mate-coherence). -/
def commonModelTensorComparison (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (X : Models D)
    (K L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar
      (D.geometricFiber X.obj).left) :=
  letI := fun x ↦ sfWeilPrimeInvertible D C.l C.different X.obj x
  canonicalCommonStagePullbackTensor C.l C.Qbar (D.geometricFrobenius X.obj).hom K L

/-- The literal pullback-composition Frobenius square at a model morphism.
Source: lem-fix-weil-operations.proof.md, ordinary pullback comparison
(blueprint: lem-pod-constructible-mate-coherence). -/
def commonModelPullbackComponent (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    {X Y : Models D} (f₀ : X ⟶ Y)
    (K : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar
      (D.geometricFiber Y.obj).left) :=
  letI := fun x ↦ sfWeilPrimeInvertible D C.l C.different X.obj x
  letI := fun y ↦ sfWeilPrimeInvertible D C.l C.different Y.obj y
  podCommonSquarePullbackComponent (X := (D.geometricFiber X.obj).left)
    (Y := (D.geometricFiber Y.obj).left) C.l C.Qbar (FrobeniusExchange.fiberMap D f₀.hom)
    (D.geometricFrobenius X.obj).hom (D.geometricFrobenius Y.obj).hom
    (D.frobenius_square_cartesian X.obj Y.obj f₀.hom).2.2.2.2.1 K

/-- A coherent lift uses the specified pullback square, its direct-image mate, and
literal common-stage compact-support exchange. Normalizations refer to the existing
canonical maps, rather than accepting arbitrary natural isomorphisms.
Source: prop-weil-operations.proof.md, sentence 1 and comparison paragraph
(blueprint: lem-pod-constructible-mate-coherence). -/
structure CommonLifts
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (A : CommonStage D C) where
  pull : ∀ {X Y : Models D} (f₀ : X ⟶ Y),
    (@SixFunctorPushStage.pull
      D _ (commonStageCategory D C) A) ((fiberModels D).map f₀) ⋙ commonFrobenius D C X ≅
      commonFrobenius D C Y ⋙ (@SixFunctorPushStage.pull
        D _ (commonStageCategory D C) A) ((fiberModels D).map f₀)
  pullNormalization : ∀ {X Y : Models D} (f₀ : X ⟶ Y)
    (K : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar
      (D.geometricFiber Y.obj).left),
    HEq ((pull f₀).app K) (commonModelPullbackComponent D C f₀ K)
  direct : ∀ {X Y : Models D} (f₀ : X ⟶ Y),
    (@SixFunctorPushStage.direct
      D _ (commonStageCategory D C) A) ((fiberModels D).map f₀) ⋙ commonFrobenius D C Y ≅
      commonFrobenius D C X ⋙ (@SixFunctorPushStage.direct
        D _ (commonStageCategory D C) A) ((fiberModels D).map f₀)
  directMate : ∀ {X Y : Models D} (f₀ : X ⟶ Y),
    (direct f₀).hom = (mateEquiv
      ((@SixFunctorPushStage.pullDirectAdjunction
        D _ (commonStageCategory D C) A) ((fiberModels D).map f₀))
      ((@SixFunctorPushStage.pullDirectAdjunction
        D _ (commonStageCategory D C) A) ((fiberModels D).map f₀)) (pull f₀).inv).natTrans
  support : ∀ {X Y : Models D} (f₀ : X ⟶ Y)
    (_c₀ : Compactification f₀.hom.left)
    (c : Compactification ((fiberModels D).map f₀).hom.left),
    (@SixFunctorPushStage.support
      D _ (commonStageCategory D C) A) ((fiberModels D).map f₀) c ⋙ commonFrobenius D C Y ≅
      commonFrobenius D C X ⋙ (@SixFunctorPushStage.support
        D _ (commonStageCategory D C) A) ((fiberModels D).map f₀) c
  supportNormalization : ∀ {X Y : Models D} (f₀ : X ⟶ Y)
    [IsSeparated f₀.hom.left] [LocallyOfFiniteType f₀.hom.left] [QuasiCompact f₀.hom.left]
    (c₀ : Compactification f₀.hom.left)
    (K : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar (D.geometricFiber X.obj).left),
    HEq ((support f₀ c₀ (FrobeniusExchange.geometricCompactification D f₀.hom c₀)).hom.app K)
      ((FrobeniusExchange.frobeniusCommonStage D C.l C.different f₀.hom
        (FrobeniusExchange.frobeniusCompactModel D f₀.hom c₀) C.Qbar).app K)
  supportConjugation : ∀ {X Y : Models D} (f₀ : X ⟶ Y)
    (c₀ : Compactification f₀.hom.left)
    (c : Compactification ((fiberModels D).map f₀).hom.left),
    (support f₀ c₀ c).hom =
      Functor.whiskerRight
        ((@SixFunctorPushStage.comparison
          D _ (commonStageCategory D C) A) ((fiberModels D).map f₀) c
          (FrobeniusExchange.geometricCompactification D f₀.hom c₀)).hom
        (commonFrobenius D C Y) ≫
      (support f₀ c₀ (FrobeniusExchange.geometricCompactification D f₀.hom c₀)).hom ≫
      Functor.whiskerLeft (commonFrobenius D C X)
        ((@SixFunctorPushStage.comparison D _ (commonStageCategory D C) A) ((fiberModels D).map f₀)
          (FrobeniusExchange.geometricCompactification D f₀.hom c₀) c).hom
  exceptional : ∀ {X Y : Models D} (f₀ : X ⟶ Y)
    (_c₀ : Compactification f₀.hom.left)
    (c : Compactification ((fiberModels D).map f₀).hom.left),
    (@SixFunctorPushStage.exceptional
      D _ (commonStageCategory D C) A) ((fiberModels D).map f₀) c ⋙ commonFrobenius D C X ≅
      commonFrobenius D C Y ⋙ (@SixFunctorPushStage.exceptional
        D _ (commonStageCategory D C) A) ((fiberModels D).map f₀) c
  exceptionalMate : ∀ {X Y : Models D} (f₀ : X ⟶ Y)
    (c₀ : Compactification f₀.hom.left)
    (c : Compactification ((fiberModels D).map f₀).hom.left),
    (exceptional f₀ c₀ c).hom = (mateEquiv
      ((@SixFunctorPushStage.exceptionalAdjunction
        D _ (commonStageCategory D C) A) ((fiberModels D).map f₀) c)
      ((@SixFunctorPushStage.exceptionalAdjunction
        D _ (commonStageCategory D C) A) ((fiberModels D).map f₀) c)
      (support f₀ c₀ c).inv).natTrans
  tensor : ∀ X : Models D,
    commonModelTensor D C X ⋙ commonFrobenius D C X ≅
      (commonFrobenius D C X).prod (commonFrobenius D C X) ⋙
        commonModelTensor D C X
  tensorNormalization : ∀ (X : Models D)
    (K L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar
      (D.geometricFiber X.obj).left),
    HEq ((tensor X).app (K, L)) (commonModelTensorComparison D C X K L)

/-- The specified pullback Weil functor. Source: lem-fix-weil-operations.proof.md
(blueprint: lem-pod-constructible-mate-coherence). -/
@[irreducible] def CommonLifts.pullFunctor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {A : CommonStage D C}
    (L : CommonLifts D C A) {X Y : Models D} (f : X ⟶ Y) :
    IsoAlgebra (commonFrobenius D C Y) ⥤ IsoAlgebra (commonFrobenius D C X) :=
  IsoAlgebra.mapOfNatIso (F := commonFrobenius D C Y)
    (G := commonFrobenius D C X)
    (L := (@SixFunctorPushStage.pull
      D _ (commonStageCategory D C) A) ((fiberModels D).map f)) (L.pull f)

/-- The specified direct-image Weil functor. Source: lem-fix-weil-operations.proof.md
(blueprint: lem-pod-constructible-mate-coherence). -/
@[irreducible] def CommonLifts.directFunctor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {A : CommonStage D C}
    (L : CommonLifts D C A) {X Y : Models D} (f : X ⟶ Y) :
    IsoAlgebra (commonFrobenius D C X) ⥤ IsoAlgebra (commonFrobenius D C Y) :=
  IsoAlgebra.mapOfNatIso (F := commonFrobenius D C X)
    (G := commonFrobenius D C Y)
    (L := (@SixFunctorPushStage.direct
      D _ (commonStageCategory D C) A) ((fiberModels D).map f)) (L.direct f)

/-- The specified compact-support Weil functor. Source: lem-fix-weil-operations.proof.md
(blueprint: lem-pod-constructible-mate-coherence). -/
@[irreducible] def CommonLifts.supportFunctor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {A : CommonStage D C}
    (L : CommonLifts D C A) {X Y : Models D} (f : X ⟶ Y)
    (c₀ : Compactification f.hom.left)
    (c : Compactification ((fiberModels D).map f).hom.left) :
    IsoAlgebra (commonFrobenius D C X) ⥤ IsoAlgebra (commonFrobenius D C Y) :=
  IsoAlgebra.mapOfNatIso (F := commonFrobenius D C X)
    (G := commonFrobenius D C Y)
    (L := (@SixFunctorPushStage.support
      D _ (commonStageCategory D C) A) ((fiberModels D).map f) c)
      (L.support f c₀ c)

/-- The specified exceptional Weil functor. Source: prop-weil-operations.proof.md
(blueprint: lem-pod-constructible-mate-coherence). -/
@[irreducible] def CommonLifts.exceptionalFunctor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {A : CommonStage D C}
    (L : CommonLifts D C A) {X Y : Models D} (f : X ⟶ Y)
    (c₀ : Compactification f.hom.left)
    (c : Compactification ((fiberModels D).map f).hom.left) :
    IsoAlgebra (commonFrobenius D C Y) ⥤ IsoAlgebra (commonFrobenius D C X) :=
  IsoAlgebra.mapOfNatIso (F := commonFrobenius D C Y)
    (G := commonFrobenius D C X)
    (L := (@SixFunctorPushStage.exceptional
      D _ (commonStageCategory D C) A) ((fiberModels D).map f) c) (L.exceptional f c₀ c)

/-- The specified tensor Weil bifunctor, using the existing product transport.
Source: lem-fix-weil-operations.proof.md
(blueprint: lem-pod-constructible-mate-coherence). -/
@[irreducible] def CommonLifts.tensorFunctor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {A : CommonStage D C}
    (L : CommonLifts D C A) (X : Models D) :
    IsoAlgebra (commonFrobenius D C X) × IsoAlgebra (commonFrobenius D C X) ⥤
      IsoAlgebra (commonFrobenius D C X) :=
  IsoAlgebra.prod (F₁ := commonFrobenius D C X)
    (F₂ := commonFrobenius D C X) ⋙ IsoAlgebra.mapOfNatIso (L.tensor X)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false in
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.leftDerivedFunctor
  HasDerivedCategory.standard integralComparisonSequenceDirectImage
  integralComparisonDerivedSequencePullback
  FrobeniusExchange.systemAdjunction FrobeniusExchange.systemSquare

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true


attribute [local irreducible] FrobeniusExchange.models FrobeniusExchange.compactRealization
  FrobeniusExchange.reductionPullbackIso FrobeniusExchange.compactAlpha
  integralDerivedPullback coefficientSequenceLimit sfIntegralConstructible
  FrobeniusExchange.systemOpen FrobeniusExchange.systemOpenExchange

end PodConstructibleMate
end WeilConjectures
