/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Sheaf.Paper.CompletedCoefficientFamilyTransportModels

/-!
# Iteration of the specified coefficient comparisons

Source: blueprint main-20261015, lem-fix-operation-reduction.proof.md, final paragraph;
the dispatched transport item's proof steps 6--7 and 11
(blueprint: def-pur-completed-coefficient-transport-expressions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u s i j k m
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
namespace WeilConjectures.CompletedCoefficientTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {S : Type s} {W : S → Scheme.{t}} (T : Transport.{t, u, s, i, j} l E W)
  {I : Type k} {location : I → S}

/-- Evaluate the recorded expressions in the complete R categories.
Source: node proof step 6
(blueprint: def-pur-completed-coefficient-transport-expressions). -/
def valueR {a : S} : CompletedOperations.Expression W location a →
    ((∀ k : I, (completeR l E (W (location k))).FullSubcategory) ⥤
      (completeR l E (W a)).FullSubcategory)
  | .input k => Pi.eval _ k
  | .unit a => (Functor.const _).obj (T.site a).r_tensor.monoidal.tensorUnit
  | .tensor P Q => (valueR P).prod' (valueR Q) ⋙
      @MonoidalCategory.tensor _ _ (T.site a).r_tensor.monoidal
  | .pullback f P => valueR P ⋙ (T.arrow f).leftR l E

/-- Identify complete-category evaluation with the specified ambient quotient operations.
The recursion uses the reflected tensor comparison and the normalized Arrow.pullback;
its coefficient unit is the same whole unit system as the substitution interface.
Source: node proof steps 6--7
(blueprint: def-pur-completed-coefficient-transport-expressions). -/
def valueRIdentification {a : S} (P : CompletedOperations.Expression W location a)
    (M : ∀ k : I, (completeR l E (W (location k))).FullSubcategory) :
    ((valueR l E T P).obj M).obj ≅
      (CompletedOperations.completedValue l E P).obj (fun k ↦ (M k).obj) :=
  match P with
  | .input _ => Iso.refl _
  | .unit a => (T.site a).r_tensor.unit ≪≫ T.system_unit a
  | .tensor P Q => (T.site a).r_tensor.tensor.app
      ((valueR l E T P).obj M, (valueR l E T Q).obj M) ≪≫
        (IntegralOnSlice.completedTensor l E (W a) none).mapIso
          (Iso.prod (valueRIdentification P M) (valueRIdentification Q M))
  | .pullback f P => (T.arrow f).pullback.app ((valueR l E T P).obj M).obj ≪≫
      (integralDerivedPullback l E f).mapIso (valueRIdentification P M)

/-- Evaluate the same expressions using C^A of ordinary tensor and inverse image.
Source: node proof step 6
(blueprint: def-pur-completed-coefficient-transport-expressions). -/
def valueA {a : S} : CompletedOperations.Expression W location a →
    ((∀ k : I, ((T.site (location k)).completeA l E).FullSubcategory) ⥤
      ((T.site a).completeA l E).FullSubcategory)
  | .input k => Pi.eval _ k
  | .unit a => (Functor.const _).obj (T.site a).a_tensor.monoidal.tensorUnit
  | .tensor P Q => (valueA P).prod' (valueA Q) ⋙
      @MonoidalCategory.tensor _ _ (T.site a).a_tensor.monoidal
  | .pullback f P => valueA P ⋙ (T.arrow f).leftA l E

/-- Iterate the actual a and b: identity at inputs, strong monoidal unit at the
coefficient unit, the inverse-a tensorator at tensor vertices, and b at pullback vertices.
Source: node proof step 6
(blueprint: def-pur-completed-coefficient-transport-expressions). -/
def expressionTransport {a : S} (P : CompletedOperations.Expression W location a)
    (M : ∀ k : I, (completeR l E (W (location k))).FullSubcategory) :
    (valueA l E T P).obj (fun k ↦ ((T.site (location k)).restriction l E).obj (M k)) ≅
      ((T.site a).restriction l E).obj ((valueR l E T P).obj M) :=
  match P with
  | .input _ => Iso.refl _
  | .unit a =>
      letI := (T.site a).r_tensor.monoidal
      letI := (T.site a).a_tensor.monoidal
      letI := (T.tensor a).monoidal
      Functor.Monoidal.εIso ((T.site a).restriction l E)
  | .tensor P Q =>
      letI := (T.site a).r_tensor.monoidal
      letI := (T.site a).a_tensor.monoidal
      letI := (T.tensor a).monoidal
      (@MonoidalCategory.tensor _ _ (T.site a).a_tensor.monoidal).mapIso
        (Iso.prod (expressionTransport P M) (expressionTransport Q M)) ≪≫
          Functor.Monoidal.μIso ((T.site a).restriction l E)
            ((valueR l E T P).obj M) ((valueR l E T Q).obj M)
  | .pullback f P => ((T.arrow f).leftA l E).mapIso (expressionTransport P M) ≪≫
      (T.adjunction f).b.app ((valueR l E T P).obj M)

/-- Parenthesis-preserving substitution on complete R expressions.
Source: the recorded completed-operation substitution recursion
(blueprint: def-pur-completed-coefficient-transport-expressions). -/
def substitutionR {J : Type m} {location' : J → S}
    (σ : ∀ k : I, CompletedOperations.Expression W location' (location k)) {a : S}
    (P : CompletedOperations.Expression W location a)
    (M : ∀ k : J, (completeR l E (W (location' k))).FullSubcategory) :
    (valueR l E T (P.substitute σ)).obj M ≅
      (valueR l E T P).obj (fun k ↦ (valueR l E T (σ k)).obj M) :=
  match P with
  | .input _ => Iso.refl _
  | .unit _ => Iso.refl _
  | .tensor P Q => (@MonoidalCategory.tensor _ _ (T.site a).r_tensor.monoidal).mapIso
      (Iso.prod (substitutionR σ P M) (substitutionR σ Q M))
  | .pullback f P => ((T.arrow f).leftR l E).mapIso (substitutionR σ P M)

/-- The same substitution recursion on complete constant-coefficient expressions.
Source: the recorded completed-operation substitution recursion
(blueprint: def-pur-completed-coefficient-transport-expressions). -/
def substitutionA {J : Type m} {location' : J → S}
    (σ : ∀ k : I, CompletedOperations.Expression W location' (location k)) {a : S}
    (P : CompletedOperations.Expression W location a)
    (M : ∀ k : J, ((T.site (location' k)).completeA l E).FullSubcategory) :
    (valueA l E T (P.substitute σ)).obj M ≅
      (valueA l E T P).obj (fun k ↦ (valueA l E T (σ k)).obj M) :=
  match P with
  | .input _ => Iso.refl _
  | .unit _ => Iso.refl _
  | .tensor P Q => (@MonoidalCategory.tensor _ _ (T.site a).a_tensor.monoidal).mapIso
      (Iso.prod (substitutionA σ P M) (substitutionA σ Q M))
  | .pullback f P => ((T.arrow f).leftA l E).mapIso (substitutionA σ P M)

/-- The actual complete R structural maps in arbitrary tensor/pullback contexts.
Source: node proof step 7
(blueprint: def-pur-completed-coefficient-transport-expressions). -/
def structureR {a : S} {P Q : CompletedOperations.Expression W location a}
    (α : CompletedOperations.StructuralMap P Q)
    (M : ∀ k : I, (completeR l E (W (location k))).FullSubcategory) :
    (valueR l E T P).obj M ≅ (valueR l E T Q).obj M :=
  match α with
  | .associator P Q R => (T.site a).r_tensor.monoidal.associator
      ((valueR l E T P).obj M) ((valueR l E T Q).obj M) ((valueR l E T R).obj M)
  | .leftUnitor P => (T.site a).r_tensor.monoidal.leftUnitor ((valueR l E T P).obj M)
  | .rightUnitor P => (T.site a).r_tensor.monoidal.rightUnitor ((valueR l E T P).obj M)
  | .symmetry P Q => (T.site a).r_tensor.symmetric.braiding
      ((valueR l E T P).obj M) ((valueR l E T Q).obj M)
  | .composition g f P => (T.compositionR f g).app ((valueR l E T P).obj M)
  | .identity _ => Iso.refl _
  | .inverse α => (structureR α M).symm
  | .compose α β => structureR α M ≪≫ structureR β M
  | .tensor α β => (@MonoidalCategory.tensor _ _ (T.site a).r_tensor.monoidal).mapIso
      (Iso.prod (structureR α M) (structureR β M))
  | .pullback f α => ((T.arrow f).leftR l E).mapIso (structureR α M)

/-- The corresponding constant-coefficient structural maps with the same contexts.
Source: node proof step 7
(blueprint: def-pur-completed-coefficient-transport-expressions). -/
def structureA {a : S} {P Q : CompletedOperations.Expression W location a}
    (α : CompletedOperations.StructuralMap P Q)
    (M : ∀ k : I, ((T.site (location k)).completeA l E).FullSubcategory) :
    (valueA l E T P).obj M ≅ (valueA l E T Q).obj M :=
  match α with
  | .associator P Q R => (T.site a).a_tensor.monoidal.associator
      ((valueA l E T P).obj M) ((valueA l E T Q).obj M) ((valueA l E T R).obj M)
  | .leftUnitor P => (T.site a).a_tensor.monoidal.leftUnitor ((valueA l E T P).obj M)
  | .rightUnitor P => (T.site a).a_tensor.monoidal.rightUnitor ((valueA l E T P).obj M)
  | .symmetry P Q => (T.site a).a_tensor.symmetric.braiding
      ((valueA l E T P).obj M) ((valueA l E T Q).obj M)
  | .composition g f P => (T.compositionA f g).app ((valueA l E T P).obj M)
  | .identity _ => Iso.refl _
  | .inverse α => (structureA α M).symm
  | .compose α β => structureA α M ≪≫ structureA β M
  | .tensor α β => (@MonoidalCategory.tensor _ _ (T.site a).a_tensor.monoidal).mapIso
      (Iso.prod (structureA α M) (structureA β M))
  | .pullback f α => ((T.arrow f).leftA l E).mapIso (structureA α M)

/-- Iterated coefficient transport commutes with the recorded simultaneous substitution
recursion, with no change of parentheses and including coefficient-unit expressions.
Source: node proof step 6
(blueprint: def-pur-completed-coefficient-transport-expressions). -/
def ExpressionSubstitutionLaw : Prop :=
  ∀ {I : Type i} {J : Type j} {location : I → S} {location' : J → S}
    (σ : ∀ k : I, CompletedOperations.Expression W location' (location k)) {a : S}
    (P : CompletedOperations.Expression W location a)
    (M : ∀ k : J, (completeR l E (W (location' k))).FullSubcategory),
    (expressionTransport l E T (P.substitute σ) M).hom ≫
        ((T.site a).restriction l E).map (substitutionR l E T σ P M).hom =
      (substitutionA l E T σ P
          (fun k ↦ ((T.site (location' k)).restriction l E).obj (M k))).hom ≫
        (valueA l E T P).map (fun k ↦ (expressionTransport l E T (σ k) M).hom) ≫
          (expressionTransport l E T P (fun k ↦ (valueR l E T (σ k)).obj M)).hom

/-- All canonical structural maps, including in nested contexts, commute with the
recursively specified coefficient transport.
Source: node proof steps 6--7
(blueprint: def-pur-completed-coefficient-transport-expressions). -/
def ExpressionStructuralLaw : Prop :=
  ∀ {I : Type i} {location : I → S} {a : S}
    {P Q : CompletedOperations.Expression W location a}
    (α : CompletedOperations.StructuralMap P Q)
    (M : ∀ k : I, (completeR l E (W (location k))).FullSubcategory),
    (structureA l E T α (fun k ↦ ((T.site (location k)).restriction l E).obj (M k))).hom ≫
        (expressionTransport l E T Q M).hom =
      (expressionTransport l E T P M).hom ≫
        ((T.site a).restriction l E).map (structureR l E T α M).hom

end WeilConjectures.CompletedCoefficientTransport
