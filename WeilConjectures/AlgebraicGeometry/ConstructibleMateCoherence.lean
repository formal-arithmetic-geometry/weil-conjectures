/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusSquareCartesian
public import WeilConjectures.AlgebraicGeometry.ConstructibleWeilModelSquares
public import WeilConjectures.AlgebraicGeometry.SixFunctorDatum
public import WeilConjectures.AlgebraicGeometry.FrobeniusGeometricExchange
public import WeilConjectures.AlgebraicGeometry.SfWeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.SemilinearFieldOperationLifts
public import WeilConjectures.AlgebraicGeometry.DerivedAutomorphismHomEvaluation
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
import WeilConjectures.CategoryTheory.MateIsoAlongEquivalences
import WeilConjectures.AlgebraicGeometry.NormalizedRationalEvaluationNaturality
import WeilConjectures.AlgebraicGeometry.NormalizedCommonEvaluationNaturality

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

/-- The assumed constructible adjunction lifts by precisely the right mate of inverse
compact-support exchange. The assertion is valid for either actual coefficient category,
and on any of the stipulated full operation domains.
Source: prop-weil-operations.proof.md, sentence 1
(blueprint: lem-pod-constructible-mate-coherence).
Proof: use lem-pod-weil-frobenius-compact-support-exchange for the specified left
comparison when it is presented as Ex_!. The present input is already that comparison
as an isomorphism. Apply lem-weil-mate-iso-along-equivalences to its inverse with both
adjunctions adj: the horizontal S is an equivalence and T is fully faithful. This gives
an invertible mate, whose three factors are def-weil-pbc-adjunction-mate. The unit
formula of lem-pur-mate-unit-compatibility followed by cancellation of G(alpha inverse)
gives the first displayed mate equation. The transpose formula followed by cancellation
of alpha inverse gives the second. Apply lem-sf-fixed-pair-adjunction-lift with this
very mate. Its carrier unit and counit are adj.unit and adj.counit; its two structure
identities are exactly those displayed here. The original triangles remain unchanged. -/
theorem adjunction_coherent
    {C : Type a} {B : Type b} [Category.{c} C] [Category.{d} B]
    (S : C ⥤ C) (T : B ⥤ B) [S.IsEquivalence] [T.IsEquivalence]
    {F : C ⥤ B} {G : B ⥤ C} (adj : F ⊣ G) (α : F ⋙ T ≅ S ⋙ F) :
    AdjunctionCoherent S T adj α := by
  have : IsIso (mateEquiv adj adj α.inv).natTrans :=
    isIso_mateEquiv_of_isEquivalence_of_fullyFaithful adj adj S T α.symm
  let β := asIso (mateEquiv adj adj α.inv).natTrans
  have hβ : (mateEquiv adj adj α.inv).natTrans = β.hom := rfl
  have hLift : PodCovariantWeilLiftSpec G β := by
    refine ⟨rfl, fun K ↦ ⟨rfl, IsoAlgebra.mapOfNatIso_obj_str β K⟩, ?_⟩
    intro K L u
    refine ⟨rfl, ?_⟩
    exact ((IsoAlgebra.mapOfNatIso β).map u).hom.h.symm
  refine ⟨inferInstance, β, hβ.symm, ?_, hLift, ?_, ?_, ?_, ?_, ?_⟩
  · intro L
    simp [β, mateEquiv]
  · intro K
    have hu := unit_mateEquiv adj adj (TwoSquare.mk _ _ _ _ α.inv) K
    rw [NatTrans.congr_app hβ] at hu
    rw [reassoc_of% hu, ← G.map_comp, Iso.inv_hom_id_app]
    simp
  · intro L
    have hc := mateEquiv_counit adj adj (TwoSquare.mk _ _ _ _ α.inv) L
    rw [NatTrans.congr_app hβ] at hc
    rw [hc]
    exact Iso.hom_inv_id_app_assoc α _ _
  · intro K
    exact IsoAlgebra.map_unit_app_comp_str adj α β hβ K
  · intro L
    exact (IsoAlgebra.map_counit_app_comp_str adj α β hβ L).symm
  · refine ⟨IsoAlgebra.mapOfNatIsoAdjunction adj α β hβ, ?_, ?_, ?_, ?_⟩
    · intro K
      rfl
    · intro L
      rfl
    · exact adj.left_triangle_components
    · exact adj.right_triangle_components

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

/-- The rational comparison package, on the original full constructible domains.
All operation and comparison choices are those of the normalized six-functor datum;
only their Frobenius lifts are asserted to exist. In particular no base scheme is
assumed separated.
Source: prop-weil-operations.proof.md, sentence 1; lem-fix-weil-operations.proof.md,
ordinary adjunctions, compositions, exchange cubes and projection
(blueprint: lem-pod-constructible-mate-coherence).
Proof: apply lem-pod-frobenius-pullback-monoidal-adjunction-coherence to the actual
pullback-composition and tensor comparisons. Its ordinary adjunction calculation
gives the direct comparison as the specified mate. Apply
lem-pod-semilinear-exchange-cube-coherence to the same model squares, relabeling
source k-structures by a_T g_T; the cube and refinement identities give the exact
support normalizations, both exchange transformations and composition comparisons.
Lemma lem-pod-weil-frobenius-compact-support-exchange makes the support comparison
invertible without separated bases. Apply adjunction_coherent and
lem-sf-fixed-pair-adjunction-lift to the constructible exceptional adjunction;
its right comparison is exactly exceptionalMate. The coefficient normalizations
in the operation datum retain the original units, counits and comparisons through
integral realization and rationalization. Lemma
lem-pod-frobenius-evaluation-projection-coherence gives the projection Weil equation
for the actual counit-defined projection followed by the proper image of the open
projection comparison. Finally lem-pod-equivariant-mates-coefficient-transport and
lem-weil-pbc-mate-pasting identify the exceptional composition with the specified
right-adjoint comparison. Already invertible comparisons lift to isomorphisms in
the existing fixed-pair category; no invertibility of exchange or projection is deduced merely
from these equations. -/
theorem rational_comparisons_coherent
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [_root_.Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (A : SixFunctorOperationDatum D C E 1 (Nat.le_refl 1)) :
    ∃ L : RationalLifts D C E A.higher.rational,
      RationalCoherence D C E A.higher L := by
  sorry

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

/-- Every canonical comparison retains its exact carrier. An existential lifted
natural transformation is precisely a proof of its Weil equation; the carrier
conditions fix the transformation uniquely. Isomorphism outputs are used only
for the comparisons already invertible in the underlying construction.
Source: prop-weil-operations.proof.md, all comparison clauses
(blueprint: lem-pod-constructible-mate-coherence). -/
def CommonCoherence
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (A : SixFunctorCommonStages D C)
    (L : CommonLifts D C A.commonStage) : Prop :=
  -- ordinaryAdjunction
  (∀ {X Y : Models D} (f : X ⟶ Y),
    AdjunctionCoherent (commonFrobenius D C Y) (commonFrobenius D C X)
      ((@SixFunctorPushStage.pullDirectAdjunction
        D _ (commonStageCategory D C) A.commonStage) ((fiberModels D).map f)) (L.pull f)) ∧
  -- exceptionalAdjunction
  (∀ {X Y : Models D} (f : X ⟶ Y)
    (c₀ : Compactification f.hom.left)
    (c : Compactification ((fiberModels D).map f).hom.left),
    AdjunctionCoherent (commonFrobenius D C X) (commonFrobenius D C Y)
      ((@SixFunctorPushStage.exceptionalAdjunction
        D _ (commonStageCategory D C) A.commonStage) ((fiberModels D).map f) c)
      (L.support f c₀ c)) ∧
  -- pullComposition
  (∀ {X Y Z : Models D} (f : X ⟶ Y) (g : Y ⟶ Z),
    ∃ w : L.pullFunctor (f ≫ g) ≅ L.pullFunctor g ⋙ L.pullFunctor f,
      ∀ K, HEq ((w.hom.app K).hom.f)
        (((@SixFunctorPushStage.pullComposition
          D _ (commonStageCategory D C) A.commonStage) ((fiberModels D).map f)
          ((fiberModels D).map g)).hom.app K.carrier)) ∧
  -- directComposition
  (∀ {X Y Z : Models D} (f : X ⟶ Y) (g : Y ⟶ Z),
    ∃ w : L.directFunctor (f ≫ g) ≅ L.directFunctor f ⋙ L.directFunctor g,
      ∀ K, HEq ((w.hom.app K).hom.f)
        ((sixFunctorDirectComposition A.commonStage ((fiberModels D).map f)
          ((fiberModels D).map g)).hom.app K.carrier)) ∧
  -- supportComparison
  (∀ {X Y : Models D} (f : X ⟶ Y)
    (c₀ d₀ : Compactification f.hom.left)
    (c d : Compactification ((fiberModels D).map f).hom.left),
    ∃ w : L.supportFunctor f c₀ c ≅ L.supportFunctor f d₀ d,
      ∀ K, HEq ((w.hom.app K).hom.f)
        (((@SixFunctorPushStage.comparison
          D _ (commonStageCategory D C) A.commonStage) ((fiberModels D).map f) c d).hom.app
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
          D _ (commonStageCategory D C) A.commonStage)
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
        ((sixFunctorExceptionalComposition A.commonStage
          ((fiberModels D).map f) ((fiberModels D).map g)
          cf cg (fiberCompositionCompactification D f g cfg)).hom.app K.carrier)) ∧
  -- directExchange
  (∀ Q : ModelSquare D,
    ∃ w : L.directFunctor Q.f ⋙ L.pullFunctor Q.g ⟶
      L.pullFunctor Q.g' ⋙ L.directFunctor Q.f',
      (∀ K, HEq ((w.app K).hom.f)
        ((A.commonStageExchange Q.fiber).stage.exchange.app K.carrier)) ∧
      (IsIso (A.commonStageExchange Q.fiber).stage.exchange → IsIso w)) ∧
  -- compactExchange
  (∀ (Q : ModelSquare D)
    (c₀ : Compactification Q.f.hom.left) (c₀' : Compactification Q.f'.hom.left),
    ∃ w : L.supportFunctor Q.f c₀ Q.fiber.compactification ⋙ L.pullFunctor Q.g ⟶
      L.pullFunctor Q.g' ⋙ L.supportFunctor Q.f' c₀' Q.fiber.compactification',
      (∀ K, HEq ((w.app K).hom.f)
        ((A.commonStageExchange Q.fiber).stage.compactExchange.app K.carrier)) ∧
      (IsIso (A.commonStageExchange Q.fiber).stage.compactExchange → IsIso w)) ∧
  -- projection
  (∀ (Q : ModelSquare D) (c₀ : Compactification Q.f.hom.left)
    (K : IsoAlgebra (commonFrobenius D C Q.X))
    (N : IsoAlgebra (commonFrobenius D C Q.Y)),
    ∃ w : (L.tensorFunctor Q.Y).obj
        ((L.supportFunctor Q.f c₀ Q.fiber.compactification).obj K, N) ⟶
      (L.supportFunctor Q.f c₀ Q.fiber.compactification).obj
        ((L.tensorFunctor Q.X).obj (K, (L.pullFunctor Q.f).obj N)),
      HEq w.hom.f (((A.commonStageExchange Q.fiber).stage.projection.app K.carrier).app N.carrier) ∧
      (IsIso (((A.commonStageExchange Q.fiber).stage.projection.app K.carrier).app N.carrier) →
        IsIso w))

/-- Common-stage comparisons and the lifted exceptional adjunction use the literal
common-stage Frobenius exchange. Every composition, exchange and projection map has
its prescribed carrier, including arbitrary Weil structures in the common category.
Source: prop-weil-operations.proof.md, sentence 1 and lem-fix-weil-operations.proof.md,
common-stage descent of adjunctions and comparisons
(blueprint: lem-pod-constructible-mate-coherence).
Proof: use the common-stage comparisons in the normalized operation datum. Descend
any finite diagram of objects, structure maps and inverse structures to a common
finite coefficient field. The rational comparison equations hold there; the supplied
scalar comparisons preserve units, counits, comparisons and their mates. Identity
and tower equations make the resulting common maps independent of representatives.
The compact-support comparison is the actual frobeniusCommonStage, invertible by
lem-pod-weil-frobenius-compact-support-exchange even on nonseparated bases. Apply
adjunction_coherent to that comparison and the given constructible exceptional
adjunction. Mate pasting identifies exceptional composition. Exchange and projection
remain transformations, acquiring inverses only on their already proved domains. -/
theorem common_comparisons_coherent
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [_root_.Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (A : SixFunctorOperationDatum D C E 1 (Nat.le_refl 1)) :
    ∃ L : CommonLifts D C A.closure.commonStage,
      CommonCoherence D C A.closure L := by
  sorry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The Hom lift's literal structure arrow, with the inverse in its first variable.
The internal-Hom functor and its permitted-pair predicate are the supplied ones.
Source: lem-fix-weil-operations.proof.md, internal Hom and evaluation
(blueprint: lem-pod-constructible-mate-coherence). -/
def homStructureMap
    {B : Type a} [Category.{b} B] (P : B ⥤ B)
    (J : ObjectProperty (Bᵒᵖ × B)) (H : J.FullSubcategory ⥤ B)
    (hJ : ∀ K : J.FullSubcategory, J ((P.op.prod P).obj K.obj))
    (κ : H ⋙ P ≅ podPairPullback P J J hJ ⋙ H)
    (K : (podWeilHomPairs P J).FullSubcategory) :
    P.obj (H.obj ((podWeilHomPairForget P J).obj K)) ⟶
      H.obj ((podWeilHomPairForget P J).obj K) :=
  κ.hom.app ((podWeilHomPairForget P J).obj K) ≫
    H.map (X := (podPairPullback P J J hJ).obj ((podWeilHomPairForget P J).obj K))
      (Y := (podWeilHomPairForget P J).obj K)
      (ObjectProperty.homMk (Prod.mkHom K.obj.1.unop.str.inv.op K.obj.2.str.hom))

/-- The exact evaluation Weil equation for the specified tensor and Hom structures.
No pair outside J occurs in this predicate.
Source: prop-weil-operations.proof.md, tensor evaluation
(blueprint: lem-pod-constructible-mate-coherence). -/
def EvaluationEquivariant
    {B : Type a} [Category.{b} B] [Preadditive B]
    (P : B ⥤ B) (T : B × B ⥤ B)
    (J : ObjectProperty (Bᵒᵖ × B)) (H : J.FullSubcategory ⥤ B)
    (SC : PodPartialClosed T J H)
    (hJ : ∀ K : J.FullSubcategory, J ((P.op.prod P).obj K.obj))
    (κ : H ⋙ P ≅ podPairPullback P J J hJ ⋙ H)
    (μ : T ⋙ P ≅ P.prod P ⋙ T) : Prop :=
  ∀ K : (podWeilHomPairs P J).FullSubcategory,
    IsIso (homStructureMap P J H hJ κ K) ∧
    μ.hom.app (H.obj ((podWeilHomPairForget P J).obj K), K.obj.1.unop.carrier) ≫
      T.map (Prod.mkHom (homStructureMap P J H hJ κ K) K.obj.1.unop.str.hom) ≫
      SC.evaluation ((podWeilHomPairForget P J).obj K) =
    P.map (SC.evaluation ((podWeilHomPairForget P J).obj K)) ≫ K.obj.2.str.hom

private theorem evaluation_equivariant_of_naturality
    {B : Type a} [Category.{b} B] [Preadditive B]
    (P : B ⥤ B) (T : B × B ⥤ B)
    (J : ObjectProperty (Bᵒᵖ × B)) (H : J.FullSubcategory ⥤ B)
    (SC : PodPartialClosed T J H)
    (hJ : ∀ K : J.FullSubcategory, J ((P.op.prod P).obj K.obj))
    (κ : H ⋙ P ≅ podPairPullback P J J hJ ⋙ H)
    (μ : T ⋙ P ≅ P.prod P ⋙ T)
    (hn : ∀ (Q R : J.FullSubcategory) (f : Q ⟶ R),
      T.map (Prod.mkHom (H.map f) (𝟙 R.obj.1.unop)) ≫ SC.evaluation R =
        T.map (Prod.mkHom (𝟙 (H.obj Q)) f.hom.1.unop) ≫
          SC.evaluation Q ≫ f.hom.2)
    (he : ∀ Q : J.FullSubcategory,
      μ.hom.app (H.obj Q, Q.obj.1.unop) ≫
        T.map (Prod.mkHom (κ.hom.app Q) (𝟙 _)) ≫
          SC.evaluation ((podPairPullback P J J hJ).obj Q) = P.map (SC.evaluation Q)) :
    EvaluationEquivariant P T J H SC hJ κ μ := by
  intro K
  let Q := (podWeilHomPairForget P J).obj K
  let R := (podPairPullback P J J hJ).obj Q
  let f : R ⟶ Q :=
    ObjectProperty.homMk (Prod.mkHom K.obj.1.unop.str.inv.op K.obj.2.str.hom)
  have hf : IsIso f := by
    apply (ObjectProperty.isIso_hom_iff f).mp
    exact ((K.obj.1.unop.str.symm.op).prod K.obj.2.str).isIso_hom
  constructor
  · dsimp only [homStructureMap]
    change IsIso (κ.hom.app Q ≫ H.map f)
    infer_instance
  · have h := congrArg
        (fun z ↦ T.map (Prod.mkHom (𝟙 (H.obj R)) K.obj.1.unop.str.hom) ≫ z)
        (hn R Q f)
    have h' : T.map (Prod.mkHom (H.map f) K.obj.1.unop.str.hom) ≫
        SC.evaluation Q = SC.evaluation R ≫ K.obj.2.str.hom := by
      change T.map (Prod.mkHom (𝟙 (H.obj R)) K.obj.1.unop.str.hom) ≫
          T.map (Prod.mkHom (H.map f) (𝟙 K.obj.1.unop.carrier)) ≫ SC.evaluation Q =
        T.map (Prod.mkHom (𝟙 (H.obj R)) K.obj.1.unop.str.hom) ≫
          T.map (Prod.mkHom (𝟙 (H.obj R)) K.obj.1.unop.str.inv) ≫
            SC.evaluation R ≫ K.obj.2.str.hom at h
      simpa only [← Category.assoc, ← T.map_comp, prod_comp, Category.id_comp,
        Category.comp_id, Iso.hom_inv_id, ← prod_id, T.map_id] using h
    change μ.hom.app (H.obj Q, Q.obj.1.unop) ≫
      T.map (Prod.mkHom (κ.hom.app Q ≫ H.map f) K.obj.1.unop.str.hom) ≫
        SC.evaluation Q = P.map (SC.evaluation Q) ≫ K.obj.2.str.hom
    rw [show Prod.mkHom (κ.hom.app Q ≫ H.map f) K.obj.1.unop.str.hom =
        Prod.mkHom (κ.hom.app Q) (𝟙 _) ≫
          Prod.mkHom (H.map f) K.obj.1.unop.str.hom by simp,
      T.map_comp, Category.assoc, h']
    have he' := congrArg (fun z ↦ z ≫ K.obj.2.str.hom) (he Q)
    dsimp only [Q, R, podWeilHomPairForget, podPairPullback, ObjectProperty.lift,
      ObjectProperty.ι, inducedFunctor, Functor.comp_obj, Functor.prod_obj,
      Functor.op_obj, IsoAlgebra.forget, IsoAlgebra.ι, Algebra.forget] at he' ⊢
    simpa only [Category.assoc] using he'

set_option linter.unusedVariables false in
/-- Evaluation for the actual rational operations. Typed parameters are fixed by
normalization to the published constructions, to avoid unfolding large derived
models repeatedly during elaboration; they introduce no replacement operation.
Source: prop-weil-operations.proof.md, tensor evaluation
(blueprint: lem-pod-constructible-mate-coherence).
Proof: normalize the supplied operations and comparisons to their published
constructions. Use normalizedRationalEvaluation_naturality on the pair arrow
(theta_K inverse, theta_L). Precompose its evaluation equation with the tensor
of the identity and theta_K, cancelling theta_K inverse against theta_K.
The evaluation square for podRationalHomComparison then gives precisely
EvaluationEquivariant. The comparison and both structures are invertible, so
homStructureMap is invertible. -/
theorem rational_evaluation_equivariant
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (X : Models D) (E : Type u) [Field E] [_root_.Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (P : sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left ⥤
      sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left)
    (hP : P = sfWeilFrobeniusPullback D C.l C.different X.obj E)
    (T : sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left ×
        sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left ⥤
      sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left)
    (hT : T = rationalModelTensor D C E X)
    (H : (constructibleRationalHomPairs C.l E (D.geometricFiber X.obj).left).FullSubcategory ⥤
      sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left)
    (hH : H = rationalDerivedInternalHom C.l E (D.geometricFiber X.obj).left)
    (SC : PodPartialClosed T (constructibleRationalHomPairs C.l E
      (D.geometricFiber X.obj).left) H)
    (hSC : HEq SC ((fun [hX : ∀ x : (D.geometricFiber X.obj).left,
        Invertible (C.l : (D.geometricFiber X.obj).left.residueField x)] ↦
      podRationalClosed C.l E (D.geometricFiber X.obj).left)
        (hX := fun x ↦ sfWeilPrimeInvertible D C.l C.different X.obj x)))
    (hJ : ∀ K : ObjectProperty.FullSubcategory
      (constructibleRationalHomPairs C.l E (D.geometricFiber X.obj).left),
      constructibleRationalHomPairs C.l E (D.geometricFiber X.obj).left
        ((P.op.prod P).obj K.obj))
    (κ : H ⋙ P ≅ podPairPullback P _ _ hJ ⋙ H)
    (hκ : ∀ K : ObjectProperty.FullSubcategory
      (constructibleRationalHomPairs C.l E (D.geometricFiber X.obj).left), HEq (κ.hom.app K)
        ((fun [hX : ∀ x : (D.geometricFiber X.obj).left,
            Invertible (C.l : (D.geometricFiber X.obj).left.residueField x)] ↦
          podRationalHomComparison C.l E (D.geometricFrobenius X.obj).hom K)
            (hX := fun x ↦ sfWeilPrimeInvertible D C.l C.different X.obj x)))
    (μ : T ⋙ P ≅ P.prod P ⋙ T)
    (hμ : ∀ K L, HEq (μ.app (K, L)) (rationalModelTensorComparison D C E X K L)) :
    EvaluationEquivariant P T _ H SC hJ κ μ := by
  let := fun x ↦ sfWeilPrimeInvertible D C.l C.different X.obj x
  subst P
  subst T
  subst H
  unfold rationalModelTensor at SC hSC μ hμ ⊢
  cases hSC
  apply evaluation_equivariant_of_naturality
  · exact normalizedRationalEvaluation_naturality C.l E (D.geometricFiber X.obj).left
  · intro Q
    have h := (podRationalHomComparison_laws C.l E
      (D.geometricFrobenius X.obj).hom).1.evaluation Q
    have hk := eq_of_heq (hκ Q)
    have hm := congrArg Iso.hom (eq_of_heq (hμ
      ((rationalDerivedInternalHom C.l E (D.geometricFiber X.obj).left).obj Q)
      Q.obj.1.unop))
    simp only [Iso.app_hom] at hm
    rw [hm, hk]
    exact h

set_option linter.unusedVariables false in
/-- The identical equation for the published common-stage operations, allowing an
independent coefficient universe and every permitted Weil pair. The normalizations
fix all data to their literal common-stage constructions.
Source: prop-weil-operations.proof.md, evaluation and common coefficients
(blueprint: lem-pod-constructible-mate-coherence).
Proof: use the common-stage evaluation-defined comparison and its laws from
lem-pod-derived-automorphism-hom-evaluation. The naturality and cancellation
calculation of rational_evaluation_equivariant works in this category itself.
Alternatively descend its finite diagram of structure maps, inverse structures,
tensor, Hom and evaluation to one common finite field, apply the rational
equality, and use the given scalar identity and tower equations. Neither route
selects a Frobenius-stable lattice or enlarges the Hom-pair domain. -/
theorem common_evaluation_equivariant
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X : Models D) (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X.obj).left ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X.obj).left)
    (hP : P = sfCommonStageWeilFrobeniusPullback D l hl X.obj Ω)
    (T : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X.obj).left ×
        generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X.obj).left ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X.obj).left)
    (hT : HEq T ((fun [hX : ∀ x : (D.geometricFiber X.obj).left,
        Invertible (l : (D.geometricFiber X.obj).left.residueField x)] ↦
      commonStageDerivedTensor l Ω (D.geometricFiber X.obj).left)
        (hX := fun x ↦ sfWeilPrimeInvertible D l hl X.obj x)))
    (H : (commonStageHomPairs l Ω (D.geometricFiber X.obj).left).FullSubcategory ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber X.obj).left)
    (hH : H = commonStageDerivedInternalHom l Ω (D.geometricFiber X.obj).left)
    (SC : PodPartialClosed T (commonStageHomPairs l Ω (D.geometricFiber X.obj).left) H)
    (hSC : HEq SC ((fun [hX : ∀ x : (D.geometricFiber X.obj).left,
        Invertible (l : (D.geometricFiber X.obj).left.residueField x)] ↦
      podCommonClosed l Ω (D.geometricFiber X.obj).left)
        (hX := fun x ↦ sfWeilPrimeInvertible D l hl X.obj x)))
    (hJ : ∀ K : (commonStageHomPairs l Ω (D.geometricFiber X.obj).left).FullSubcategory,
      commonStageHomPairs l Ω (D.geometricFiber X.obj).left ((P.op.prod P).obj K.obj))
    (κ : H ⋙ P ≅ podPairPullback P _ _ hJ ⋙ H)
    (hκ : ∀ K : (commonStageHomPairs l Ω (D.geometricFiber X.obj).left).FullSubcategory,
      HEq (κ.hom.app K) ((fun [hX : ∀ x : (D.geometricFiber X.obj).left,
          Invertible (l : (D.geometricFiber X.obj).left.residueField x)] ↦
        podCommonHomComparison l Ω (D.geometricFrobenius X.obj).hom K)
          (hX := fun x ↦ sfWeilPrimeInvertible D l hl X.obj x)))
    (μ : T ⋙ P ≅ P.prod P ⋙ T)
    (hμ : ∀ K L, HEq (μ.app (K, L))
      ((fun [hX : ∀ x : (D.geometricFiber X.obj).left,
          Invertible (l : (D.geometricFiber X.obj).left.residueField x)] ↦
        canonicalCommonStagePullbackTensor l Ω (D.geometricFrobenius X.obj).hom K L)
          (hX := fun x ↦ sfWeilPrimeInvertible D l hl X.obj x))) :
    EvaluationEquivariant P T _ H SC hJ κ μ := by
  let := fun x ↦ sfWeilPrimeInvertible D l hl X.obj x
  subst P
  cases eq_of_heq hT
  subst H
  cases eq_of_heq hSC
  apply evaluation_equivariant_of_naturality
  · exact normalizedCommonEvaluation_naturality l Ω (D.geometricFiber X.obj).left
  · intro Q
    have h := (podCommonHomComparison_laws l Ω
      (D.geometricFrobenius X.obj).hom).evaluation Q
    have hk := eq_of_heq (hκ Q)
    have hm := congrArg Iso.hom (eq_of_heq (hμ
      ((commonStageDerivedInternalHom l Ω (D.geometricFiber X.obj).left).obj Q)
      Q.obj.1.unop))
    simp only [Iso.app_hom] at hm
    rw [hm, hk]
    exact h
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

private theorem systemPullback_equivalence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [_root_.Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (integralComparisonDerivedSequencePullback l E g).IsEquivalence := by
  let F := integralComparisonDerivedSequencePullback l E g
  let G := integralComparisonDerivedSequencePullback l E (inv g)
  let a : F ⋙ G ≅ 𝟭 _ :=
    (integralComparisonSystemComposition l E (inv g) g).symm ≪≫
      eqToIso (congrArg (integralComparisonDerivedSequencePullback l E)
        (IsIso.inv_hom_id g)) ≪≫ integralComparisonSystemUnit l E Y
  let b : G ⋙ F ≅ 𝟭 _ :=
    (integralComparisonSystemComposition l E g (inv g)).symm ≪≫
      eqToIso (congrArg (integralComparisonDerivedSequencePullback l E)
        (IsIso.hom_inv_id g)) ≪≫ integralComparisonSystemUnit l E X
  exact (CategoryTheory.Equivalence.mk F G a.symm b).isEquivalence_functor

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true


private theorem systemCompactExchange_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [_root_.Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y)
    [IsIso gB] [IsIso gY] (wp : gB ≫ c.g = c.g ≫ gY)
    (sj : IsPullback gX c.i c.i gB) :
    IsIso (FrobeniusExchange.systemCompactExchange l E c gX gB gY wp sj) := by
  have := systemPullback_equivalence l E gB
  have := systemPullback_equivalence l E gY
  have := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (FrobeniusExchange.systemAdjunction l E c.g)
    (FrobeniusExchange.systemAdjunction l E c.g)
    (integralComparisonDerivedSequencePullback l E gY)
    (integralComparisonDerivedSequencePullback l E gB)
    (FrobeniusExchange.systemSquare l E c.g gB gY wp)
  unfold FrobeniusExchange.systemCompactExchange
  have hm : IsIso (FrobeniusExchange.systemExchange l E c.g gB gY wp) := by
    change IsIso (mateEquiv (FrobeniusExchange.systemAdjunction l E c.g)
      (FrobeniusExchange.systemAdjunction l E c.g)
      (FrobeniusExchange.systemSquare l E c.g gB gY wp).hom).natTrans
    infer_instance
  infer_instance

attribute [local irreducible] FrobeniusExchange.models FrobeniusExchange.compactRealization
  FrobeniusExchange.reductionPullbackIso FrobeniusExchange.compactAlpha
  integralDerivedPullback coefficientSequenceLimit sfIntegralConstructible
  FrobeniusExchange.systemOpen FrobeniusExchange.systemOpenExchange

private theorem compactIntegral_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [_root_.Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (k : Type u) [Field k] (hl : IsUnit (l : k))
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (c : Compactification f) (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y)
    [IsIso gX] [IsIso gB] [IsIso gY] (wp : gB ≫ c.g = c.g ≫ gY)
    (sj : IsPullback gX c.i c.i gB) :
    IsIso (FrobeniusExchange.compactIntegral l E k hl f c gX gB gY wp sj) := by
  have := systemCompactExchange_isIso l E c gX gB gY wp sj
  have ha : IsIso (FrobeniusExchange.compactAlpha l E k hl f c gY) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact FrobeniusExchange.compactAlpha_isIso l E k hl f c gY
  have hb : IsIso (FrobeniusExchange.compactBeta l E k hl f c gX) := by
    exact (Functor.isoWhiskerRight (FrobeniusExchange.reductionPullbackIso l E gX).symm
      ((FrobeniusExchange.systemDerivedOpen l E c.i ⋙ FrobeniusExchange.systemDirect l E c.g) ⋙
        coefficientSequenceLimit l E Y) ≪≫
      Functor.isoWhiskerLeft (constructibleIntegralPullback l E gX)
        (FrobeniusExchange.compactRealization l E k hl f c).symm).isIso_hom
  have hc : IsIso (FrobeniusExchange.compactIntegralAmbient l E k hl f c
      gX gB gY wp sj) := by
    unfold FrobeniusExchange.compactIntegralAmbient
    infer_instance
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  apply (ObjectProperty.isIso_hom_iff _).mp
  dsimp only [FrobeniusExchange.compactIntegral, ObjectProperty.homMk]
  change IsIso ((FrobeniusExchange.compactIntegralAmbient l E k hl f c
    gX gB gY wp sj).app K)
  infer_instance

private instance localizedTransformation_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [_root_.Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y : Scheme.{u}}
    (F G : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y)
    [F.Additive] [G.Additive]
    [F.Linear (Padic.coefficientExtensionIntegers l E)]
    [G.Linear (Padic.coefficientExtensionIntegers l E)]
    (τ : F ⟶ G) [IsIso τ] : IsIso (FrobeniusExchange.localizedTransformation l E F G τ) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  change IsIso ((sfRationalConstructibleLocalization l E Y).map (τ.app K.obj))
  infer_instance

private theorem compactRational_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [_root_.Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (k : Type u) [Field k] (hl : IsUnit (l : k))
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [xft : LocallyOfFiniteType (X ↘ Spec (.of k))]
    [xqc : QuasiCompact (X ↘ Spec (.of k))]
    [yft : LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [yqc : QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [fo : f.IsOver (Spec (.of k))]
    [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (c : Compactification f) (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y)
    [hgX : IsIso gX] [hgB : IsIso gB] [hgY : IsIso gY] (wp : gB ≫ c.g = c.g ≫ gY)
    (sj : IsPullback gX c.i c.i gB) :
    IsIso (FrobeniusExchange.modelRationalExchange l k hl f gX gY
      (.compact c gB wp sj) E) := by
  have := compactIntegral_isIso l E k hl f c gX gB gY wp sj
  have hi : IsIso (FrobeniusExchange.modelExchange l k hl f gX gY
      (.compact c gB wp sj) E) := by
    exact inferInstanceAs
      (IsIso (FrobeniusExchange.compactIntegral l E k hl f c gX gB gY wp sj))
  let := (FrobeniusExchange.modelSource_linear l k hl f gX gY (.compact c gB wp sj) E).1
  let := (FrobeniusExchange.modelSource_linear l k hl f gX gY (.compact c gB wp sj) E).2
  let := (FrobeniusExchange.modelTarget_linear l k hl f gX gY (.compact c gB wp sj) E).1
  let := (FrobeniusExchange.modelTarget_linear l k hl f gX gY (.compact c gB wp sj) E).2
  let τ : FrobeniusExchange.modelSource l k hl f gX gY (.compact c gB wp sj) E ⟶
      FrobeniusExchange.modelTarget l k hl f gX gY (.compact c gB wp sj) E :=
    by
      delta FrobeniusExchange.modelSource FrobeniusExchange.modelTarget
      exact FrobeniusExchange.modelExchange l k hl f gX gY (.compact c gB wp sj) E
  have hτ : IsIso τ := by
    dsimp only [τ]
    delta FrobeniusExchange.modelSource FrobeniusExchange.modelTarget
    exact hi
  have hloc := localizedTransformation_isIso l E _ _ τ
  have hresult := ((eqToIso (FrobeniusExchange.modelRationalSource_eq l k hl f gX gY
      (.compact c gB wp sj) E)).symm ≪≫
    asIso (FrobeniusExchange.localizedTransformation l E _ _ τ) ≪≫
      eqToIso (FrobeniusExchange.modelRationalTarget_eq l k hl f gX gY
        (.compact c gB wp sj) E)).isIso_hom
  dsimp only [FrobeniusExchange.modelRationalExchange, τ, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, id, FrobeniusExchange.modelSource, FrobeniusExchange.modelTarget] at hresult ⊢
  delta FrobeniusExchange.modelRationalExchange FrobeniusExchange.modelSource
    FrobeniusExchange.modelTarget at hresult ⊢
  exact hresult

/-- The very compact-support Frobenius exchange used in the normalizations is
invertible on the rational and common-stage constructible categories even for
nonseparated models. Only the relative morphism is assumed separated.
Source: prop-weil-operations.proof.md, Frobenius-square clause
(blueprint: lem-pod-constructible-mate-coherence).
Proof: apply lem-pod-weil-frobenius-compact-support-exchange to the actual closed
constructible operation domains and their prescribed integral realizations. The
finite proper mate is invertible because horizontal transport is an equivalence;
the open base-change map is invertible as well. Reduction identifies every
positive finite-level map with that composite. Derived completeness annihilates
the cone, so the integral map is invertible. Rationalization preserves its inverse.
The normalized coefficient comparison identifies it with frobeniusRational.
At common stages represent objects and arrows over a finite coefficient field;
the scalar comparisons and their identity and tower equations give the same
inverse class, precisely frobeniusCommonStage. This argument never assumes that
the model structure morphisms are separated, or that the Frobenius maps are k-linear. -/
theorem frobenius_exchanges_isIso
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (c₀ : Compactification f₀.left)
    (E : Type u) [Field E] [_root_.Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Ω : Type v) [Field Ω] [_root_.Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] :
    IsIso (FrobeniusExchange.frobeniusRational D l hl E f₀
      (FrobeniusExchange.frobeniusCompactModel D f₀ c₀)) ∧
    IsIso (FrobeniusExchange.frobeniusCommonStage D l hl f₀
      (FrobeniusExchange.frobeniusCompactModel D f₀ c₀) Ω) := by
  let xft : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D X₀).1
  let xqc : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D X₀).2
  let yft : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).1
  let yqc : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).2
  have fo : (FrobeniusExchange.fiberMap D f₀).IsOver (Spec (.of D.k)) := by
    exact inferInstanceAs
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left.IsOver
        (Spec (.of D.k)))
  let := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  let fs := (FrobeniusExchange.fiberMap_properties D f₀).1
  let fft := (FrobeniusExchange.fiberMap_properties D f₀).2.1
  let fqc := (FrobeniusExchange.fiberMap_properties D f₀).2.2
  have hgX : IsIso (FrobeniusExchange.galois D X₀) :=
    (D.geometricFrobenius X₀).isIso_hom
  have hgY : IsIso (FrobeniusExchange.galois D Y₀) :=
    (D.geometricFrobenius Y₀).isIso_hom
  have hgB : IsIso (FrobeniusExchange.galois D (zlCompactificationMiddle D f₀ c₀)) :=
    (D.geometricFrobenius (zlCompactificationMiddle D f₀ c₀)).isIso_hom
  constructor
  · unfold FrobeniusExchange.frobeniusRational FrobeniusExchange.frobeniusCompactModel
    exact compactRational_isIso (X := (D.geometricFiber X₀).left)
      (Y := (D.geometricFiber Y₀).left) l _ D.k (zlClosurePrimeUnit D l hl)
      (FrobeniusExchange.fiberMap D f₀) (FrobeniusExchange.geometricCompactification D f₀ c₀)
      (FrobeniusExchange.galois D X₀)
      (FrobeniusExchange.galois D (zlCompactificationMiddle D f₀ c₀))
      (FrobeniusExchange.galois D Y₀) _ _ (hgX := hgX) (hgB := hgB) (hgY := hgY)
      (xft := xft) (xqc := xqc) (yft := yft) (yqc := yqc) (fo := fo)
      (fs := fs) (fft := fft) (fqc := fqc)
  · unfold FrobeniusExchange.frobeniusCommonStage FrobeniusExchange.commonStageExchange
    apply CategoryTheory.StageSystem.Morphism.isIso_descNatTrans
    intro i
    dsimp only [FrobeniusExchange.stageExchange, FrobeniusExchange.frobeniusCompactModel]
    exact compactRational_isIso (X := (D.geometricFiber X₀).left)
      (Y := (D.geometricFiber Y₀).left) l _ D.k (zlClosurePrimeUnit D l hl)
      (FrobeniusExchange.fiberMap D f₀) (FrobeniusExchange.geometricCompactification D f₀ c₀)
      (FrobeniusExchange.galois D X₀)
      (FrobeniusExchange.galois D (zlCompactificationMiddle D f₀ c₀))
      (FrobeniusExchange.galois D Y₀) _ _ (hgX := hgX) (hgB := hgB) (hgY := hgY)
      (xft := xft) (xqc := xqc) (yft := yft) (yqc := yqc) (fo := fo)
      (fs := fs) (fft := fft) (fqc := fqc)

end PodConstructibleMate
end WeilConjectures
