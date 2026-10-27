/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q30 and H8
-/
module

public import Sheaf.CategoryTheory.SystemDerivedTransitionCoherence
public import Sheaf.CategoryTheory.SystemLevelLeftExtensionBasic
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.CategoryTheory.Functor.OfSequence
import Sheaf.CategoryTheory.SystemScalarGenerators
import Sheaf.CategoryTheory.SystemDerivedTransitionUnit
import Sheaf.CategoryTheory.EquivalenceAdjunctionComparison
import all Sheaf.CategoryTheory.DerivedExactSquareComposition
import all Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares
import Sheaf.CategoryTheory.DerivedCategory.NormalizedAdjunctionComposition
import all Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all Sheaf.CategoryTheory.DerivedCategory.ConstantTowerNormalization
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import Sheaf.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Sheaf.CategoryTheory.DerivedCategory.DerivedMateComparison
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.SystemDerivedEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass

/-! # Coherent transport of strict quotient systems

Source: def-pur-section-invariant, finite-clopen expansion, steps 2--3 and 5;
Stacks 03D7, 03EK, 015F, 06YY and 07A6
(blueprint: lem-pur-ring-iso-quotient-system-transport).

The structures below spell out the normalization of the equivalence, its scalar
comparisons and its whole-system derived reduction. They are interfaces for this
single theorem. All module categories, restrictions, tensors, adjunctions and
localizations are the recorded library constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance 11000] hasSheafCompose_of_preservesLimitsOfSize
attribute [local instance 11000] SheafOfModules.instPreadditive
attribute [local instance 11000] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance 20000] SheafOfModules.systemEvaluationAdditive
  SheafOfModules.systemEvaluationLimits SheafOfModules.systemEvaluationColimits

attribute [local instance 12000] SheafOfModules.systemRingHasDerived
attribute [local instance 12000] SheafOfModules.strictRingSystemHasDerived
attribute [local instance 12000] SheafOfModules.strictRingSystemAbelian
attribute [local instance 12000] SheafOfModules.instAbelian

namespace SheafOfModules.QuotientIsoTransport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- Use the specified sheafification adjunction directly.
Source: Stacks 03DA (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
theorem moduleWeakSheafify : HasWeakSheafify J AddCommGrpCat.{w} :=
  HasSheafify.isRightAdjoint

attribute [local instance 20000] moduleWeakSheafify

/-- Module sheaves in the coefficient universe, using the recorded category.
Source: Stacks 03DA (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
abbrev Modules (R : Sheaf J CommRingCat.{w}) :=
  ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)

/-- Scalar transport is literally restriction along the inverse ring isomorphism.
Source: Stacks 03CZ (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def transport {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) : Modules R ⥤ Modules S :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map a.inv)

/-- Additivity for inverse scalar restriction.
Source: Stacks 03D7 (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
instance transportAdditive {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    (transport a).Additive := by
  unfold transport
  infer_instance

/-- Preservation of finite limits for inverse scalar restriction.
Source: Stacks 03D7 (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
instance transportLimits {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    PreservesFiniteLimits (transport a) := by
  unfold transport
  infer_instance

/-- Preservation of finite colimits for inverse scalar restriction.
Source: Stacks 03D7 (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
instance transportColimits {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    PreservesFiniteColimits (transport a) := by
  unfold transport
  infer_instance

attribute [local instance 21000] transportAdditive transportLimits transportColimits

/-- The canonical derived comparison for an exact commuting square.
Source: Stacks 015F (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def derivedSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (rho : restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) ⋙
        transport e ≅ transport e' ⋙
          restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)) :
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).mapDerivedCategory ⋙
        (transport e).mapDerivedCategory ≅
      (transport e').mapDerivedCategory ⋙
        (restrictScalars
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso rho ≪≫ Functor.mapDerivedCategoryCompIso _ _

/-- Abstract comparison data with its specified normalization predicate.
Source: Stacks 03D7, 015F and 06YY
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
structure ScalarComparisonData
    (X0 : Sort*)
    (X1 : Sort*)
    (X2 : Sort*)
    (P : ∀ (restriction : X0) (ordinary : X1) (derived : X2), Prop) where
  restriction : X0
  ordinary : X1
  derived : X2
  conditions : P restriction ordinary derived

/-- Normalized scalar comparison for one commuting coefficient square. The Hom
identities identify the entire adjunctions and therefore both their units and counits.
Source: Stacks 03D7, 03EK, 06YY, 07A6
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def ScalarSquareConditions {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (A : SystemScalarModel a) (B : SystemScalarModel b)
    (restriction : restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) ⋙
      transport e ≅ transport e' ⋙
        restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b))
    (ordinary : A.model.E ⋙ transport e' ≅ transport e ⋙ B.model.E)
    (derived : A.model.T ⋙ (transport e').mapDerivedCategory ≅
    (transport e).mapDerivedCategory ⋙ B.model.T) : Prop :=
  (∀ (M : Modules R') (U : Cᵒᵖ) (x : M.val.obj U),
      (restriction.hom.app M).val.app U x = x) ∧
    (∀ (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (r : R'.obj.obj U),
      (ordinary.hom.app M).val.app U (systemModelTmul A.model M U r x) =
        systemModelTmul B.model ((transport e).obj M) U (e'.hom.hom.app U r) x) ∧
    (∀ (M : Modules R) (N : Modules R') (f : A.model.E.obj M ⟶ N),
      B.ordinaryAdj.homEquiv _ _ (ordinary.inv.app M ≫ (transport e').map f) =
        (transport e).map (A.ordinaryAdj.homEquiv _ _ f) ≫ restriction.hom.app N) ∧
    (∀ (P : CochainComplex (Modules R) ℤ),
      derived.hom.app (DerivedCategory.Q.obj P) ≫
          B.model.T.map ((transport e).mapDerivedCategoryFactors.hom.app P) ≫
          B.model.ε.app (((transport e).mapHomologicalComplex (.up ℤ)).obj P) =
        (transport e').mapDerivedCategory.map (A.model.ε.app P) ≫
          (transport e').mapDerivedCategoryFactors.hom.app
            ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)) ∧
    (∀ (M : DerivedCategory (Modules R)) (N : DerivedCategory (Modules R'))
      (f : A.model.T.obj M ⟶ N),
      B.adjunction.homEquiv _ _ (derived.inv.app M ≫ (transport e').mapDerivedCategory.map f) =
        (transport e).mapDerivedCategory.map (A.adjunction.homEquiv _ _ f) ≫
          (derivedSquare a b e e' restriction).hom.app N)

/-- Normalized scalar comparison for one commuting coefficient square. The Hom
identities identify the entire adjunctions and therefore both their units and counits.
Source: Stacks 03D7, 03EK, 06YY, 07A6
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
abbrev ScalarSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (A : SystemScalarModel a) (B : SystemScalarModel b) :=
  ScalarComparisonData
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) ⋙
      transport e ≅ transport e' ⋙
        restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b))
    (A.model.E ⋙ transport e' ≅ transport e ⋙ B.model.E)
    (A.model.T ⋙ (transport e').mapDerivedCategory ≅
    (transport e).mapDerivedCategory ⋙ B.model.T)
    (fun restriction ordinary derived ↦
      ScalarSquareConditions a b e e' A B  restriction ordinary derived)

/-- Abstract comparison data with its specified normalization predicate.
Source: Stacks 03D7, 015F and 06YY
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
structure ReductionComparisonData
    (X0 : Sort*)
    (X1 : ∀ (ordinary : X0), Sort*)
    (X2 : ∀ (ordinary : X0), Sort*)
    (X3 : Sort*)
    (X4 : ∀ (ordinary : X0) (additive : X1 ordinary) (derived : X3), Sort*)
    (X5 : ∀ (derived : X3), Sort*)
    (P : ∀ (ordinary : X0) (additive : X1 ordinary) (evaluation : X2 ordinary)
      (derived : X3) (counit : X4 ordinary additive derived)
      (derivedEvaluation : X5 derived), Prop) where
  ordinary : X0
  additive : X1 ordinary
  evaluation : X2 ordinary
  derived : X3
  counit : X4 ordinary additive derived
  derivedEvaluation : X5 derived
  conditions : P ordinary additive evaluation derived counit derivedEvaluation

/-- The actual strict reduction, with its sheafified pure tensors, all horizontal
maps and the universal derived reduction into the ordinary derived system category.
Source: Stacks 03EK, 06YY; sequence-site refinement of def-pur-section-invariant
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def ReductionConditions (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J))
    (ordinary : Modules c.pt ⥤ StrictRingSystem B)
    [additive : ordinary.Additive]
    (evaluation : ∀ n : ℕ, ordinary ⋙ systemEvaluation B n ≅ (A (c.π.app (op n))).model.E)
    (derived : DerivedCategory (Modules c.pt) ⥤ DerivedCategory (StrictRingSystem B))
    (counit : DerivedCategory.Q ⋙ derived ⟶
    ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (derivedEvaluation : ∀ n : ℕ,
    derived ⋙ derivedSystemEvaluation B n ≅ (A (c.π.app (op n))).model.T) : Prop :=
  (∀ (M : Modules c.pt) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ)
      (r : (B.obj (op n)).obj.obj U) (x : M.val.obj U),
      ((evaluation m).hom.app M).val.app U
        (((ordinary.obj M).transition h).val.app U
          (((evaluation n).inv.app M).val.app U
            (systemModelTmul (A (c.π.app (op n))).model M U r x))) =
        systemModelTmul (A (c.π.app (op m))).model M U
          ((B.map (homOfLE h).op).hom.app U r) x) ∧
    (derived.IsLeftDerivedFunctor counit (HomologicalComplex.quasiIso _ (.up ℤ))) ∧
    (Functor.HasPointwiseLeftDerivedFunctor
      (ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        (HomologicalComplex.quasiIso _ (.up ℤ))) ∧
    (∀ (P : CochainComplex (Modules c.pt) ℤ),
      P.IsKFlatIndependentCoefficients → (∀ i : ℤ, IsFlatOnSite (R := c.pt) (P.X i)) →
        IsIso (counit.app P)) ∧
    (∀ (n : ℕ) (P : CochainComplex (Modules c.pt) ℤ),
      (derivedEvaluation n).hom.app (DerivedCategory.Q.obj P) ≫
          (A (c.π.app (op n))).model.ε.app P =
        (derivedSystemEvaluation B n).map (counit.app P) ≫
          (systemEvaluation B n).mapDerivedCategoryFactors.hom.app
            ((ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (evaluation n) (.up ℤ)).hom.app P))

/-- The actual strict reduction, with its sheafified pure tensors, all horizontal
maps and the universal derived reduction into the ordinary derived system category.
Source: Stacks 03EK, 06YY; sequence-site refinement of def-pur-section-invariant
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
abbrev Reduction (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) :=
  ReductionComparisonData
    (Modules c.pt ⥤ StrictRingSystem B)
    (fun ordinary ↦
      ordinary.Additive)
    (fun ordinary ↦
      ∀ n : ℕ, ordinary ⋙ systemEvaluation B n ≅ (A (c.π.app (op n))).model.E)
    (DerivedCategory (Modules c.pt) ⥤ DerivedCategory (StrictRingSystem B))
    (fun ordinary additive derived ↦
      letI := additive; DerivedCategory.Q ⋙ derived ⟶
    ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (fun derived ↦
      ∀ n : ℕ,
    derived ⋙ derivedSystemEvaluation B n ≅ (A (c.π.app (op n))).model.T)
    (fun ordinary additive evaluation derived counit derivedEvaluation ↦
      ReductionConditions B c A (additive := additive) ordinary evaluation derived counit
        derivedEvaluation)

/-- The reduction's recorded additive structure.
Source: Stacks 03EK (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
instance Reduction.additive (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (D : Reduction B c A) : D.ordinary.Additive :=
  ReductionComparisonData.additive D

/-- The canonical adjoint of the actual derived transition. No inverse limit is used.
Source: Stacks 07A6 (blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def adjointTransition (A : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n)
    (M : DerivedCategory (StrictRingSystem B)) :=
  ((systemDerivedTensorAdj A B h).homEquiv _ _).symm ((systemDerivedTransition B h).app M)

/-- Abstract comparison data with its specified normalization predicate.
Source: Stacks 03D7, 015F and 06YY
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
structure TransportComparisonData
    (X0 : Sort*)
    (X1 : ∀ (equivalence : X0), Sort*)
    (X2 : ∀ (equivalence : X0), Sort*)
    (X3 : ∀ (equivalence : X0), Sort*)
    (X4 : Sort*)
    (X5 : ∀ (equivalence : X0) (additive : X1 equivalence) (derivedEquivalence : X4), Sort*)
    (X6 : ∀ (equivalence : X0), Sort*)
    (X7 : ∀ (derivedEquivalence : X4), Sort*)
    (X8 : Sort*)
    (X9 : Sort*)
    (X10 : ∀ (equivalence : X0) (reductionR : X8) (reductionS : X9), Sort*)
    (X11 : ∀ (derivedEquivalence : X4) (reductionR : X8) (reductionS : X9), Sort*)
    (X12 : Sort*)
    (X13 : Sort*)
    (P : ∀ (equivalence : X0) (additive : X1 equivalence) (limits : X2 equivalence)
      (colimits : X3 equivalence) (derivedEquivalence : X4)
      (localization : X5 equivalence additive derivedEquivalence) (level : X6 equivalence)
      (derivedLevel : X7 derivedEquivalence) (reductionR : X8) (reductionS : X9)
      (reduction : X10 equivalence reductionR reductionS)
      (derivedReduction : X11 derivedEquivalence reductionR reductionS)
      (projection : X12) (quotient : X13), Prop) where
  equivalence : X0
  additive : X1 equivalence
  limits : X2 equivalence
  colimits : X3 equivalence
  derivedEquivalence : X4
  localization : X5 equivalence additive derivedEquivalence
  level : X6 equivalence
  derivedLevel : X7 derivedEquivalence
  reductionR : X8
  reductionS : X9
  reduction : X10 equivalence reductionR reductionS
  derivedReduction : X11 derivedEquivalence reductionR reductionS
  projection : X12
  quotient : X13
  conditions : P equivalence additive limits colimits derivedEquivalence localization level
    derivedLevel reductionR reductionS reduction derivedReduction projection quotient

/-- Complete strict-system coefficient transport, including the normalization of
localization, reduction and every adjoint transition.
Source: def-pur-section-invariant, finite-clopen expansion; Stacks 03D7 and 015F
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
def CoherentTransportConditions (R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (a : R ≅ S)
    (c : Cone R) (d : Cone S) (e : c.pt ≅ d.pt)
    (A : SystemScalarAssignment (J := J))
    (equivalence : StrictRingSystem R ≌ StrictRingSystem S)
    [additive : equivalence.functor.Additive]
    [limits : PreservesFiniteLimits equivalence.functor]
    [colimits : PreservesFiniteColimits equivalence.functor]
    (derivedEquivalence :
      DerivedCategory (StrictRingSystem R) ≌ DerivedCategory (StrictRingSystem S))
    (localization : DerivedCategory.Q ⋙ derivedEquivalence.functor ≅
    equivalence.functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (level : ∀ n : ℕ, equivalence.functor ⋙ systemEvaluation S n ≅
    systemEvaluation R n ⋙ transport (a.app (op n)))
    (derivedLevel : ∀ n : ℕ, derivedEquivalence.functor ⋙ derivedSystemEvaluation S n ≅
    derivedSystemEvaluation R n ⋙ (transport (a.app (op n))).mapDerivedCategory)
    (reductionR : Reduction R c A)
    (reductionS : Reduction S d A)
    (reduction : reductionR.ordinary ⋙ equivalence.functor ≅ transport e ⋙ reductionS.ordinary)
    (derivedReduction : reductionR.derived ⋙ derivedEquivalence.functor ≅
    (transport e).mapDerivedCategory ⋙ reductionS.derived)
    (projection : ∀ n : ℕ, ScalarSquare (c.π.app (op n)) (d.π.app (op n)) e (a.app (op n))
    (A (c.π.app (op n))) (A (d.π.app (op n))))
    (quotient : ∀ {m n : ℕ} (h : m ≤ n),
    ScalarSquare (R.map (homOfLE h).op) (S.map (homOfLE h).op)
      (a.app (op n)) (a.app (op m))
      (A (R.map (homOfLE h).op)) (A (S.map (homOfLE h).op))) : Prop :=
  (∀ (M : StrictRingSystem R) (n : ℕ),
      (equivalence.functor.obj M).level n = (transport (a.app (op n))).obj (M.level n)) ∧
    (∀ (M : StrictRingSystem R) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ),
      HEq (fun x ↦ ((equivalence.functor.obj M).transition h).val.app U x)
        (fun x ↦ (M.transition h).val.app U x)) ∧
    (∀ {M N : StrictRingSystem R} (f : M ⟶ N) (n : ℕ) (U : Cᵒᵖ),
      HEq (fun x ↦ ((equivalence.functor.map f).app n).val.app U x)
        (fun x ↦ (f.app n).val.app U x)) ∧
    (derivedEquivalence.functor = equivalence.functor.mapDerivedCategory) ∧
    (HEq localization equivalence.functor.mapDerivedCategoryFactors) ∧
    (∀ (n : ℕ) (M : StrictRingSystem R) (U : Cᵒᵖ) (x : M.level n |>.val.obj U),
      HEq (((level n).inv.app M).val.app U x) x) ∧
    (∀ (n : ℕ) (P : CochainComplex (StrictRingSystem R) ℤ),
      (derivedLevel n).hom.app (DerivedCategory.Q.obj P) ≫
          (transport (a.app (op n))).mapDerivedCategory.map
            ((systemEvaluation R n).mapDerivedCategoryFactors.hom.app P) ≫
          (transport (a.app (op n))).mapDerivedCategoryFactors.hom.app
            (((systemEvaluation R n).mapHomologicalComplex (.up ℤ)).obj P) =
        (derivedSystemEvaluation S n).map (localization.hom.app P) ≫
          (systemEvaluation S n).mapDerivedCategoryFactors.hom.app
            ((equivalence.functor.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (level n) (.up ℤ)).hom.app P)) ∧
    (∀ (M : Modules c.pt) (n : ℕ) (U : Cᵒᵖ)
      (r : (R.obj (op n)).obj.obj U) (x : M.val.obj U),
      HEq (((systemEvaluation S n).map (reduction.hom.app M)).val.app U
        (((level n).inv.app (reductionR.ordinary.obj M)).val.app U
          (((reductionR.evaluation n).inv.app M).val.app U
            (systemModelTmul (A (c.π.app (op n))).model M U r x))))
        (((reductionS.evaluation n).inv.app ((transport e).obj M)).val.app U
          (systemModelTmul (A (d.π.app (op n))).model ((transport e).obj M) U
            ((a.app (op n)).hom.hom.app U r) x))) ∧
    (∀ (P : CochainComplex (Modules c.pt) ℤ),
      derivedReduction.hom.app (DerivedCategory.Q.obj P) ≫
          reductionS.derived.map ((transport e).mapDerivedCategoryFactors.hom.app P) ≫
          reductionS.counit.app (((transport e).mapHomologicalComplex (.up ℤ)).obj P) =
        derivedEquivalence.functor.map (reductionR.counit.app P) ≫
          localization.hom.app ((reductionR.ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex reduction (.up ℤ)).hom.app P)) ∧
    (∀ (n : ℕ) (M : systemLevel R n),
      (transport (a.app (op n))).map
          (((systemTensorCoherence A).ordinaryUnit R n).hom.app M) =
        (quotient (Nat.le_refl n)).ordinary.hom.app M ≫
          ((systemTensorCoherence A).ordinaryUnit S n).hom.app
            ((transport (a.app (op n))).obj M)) ∧
    (∀ {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) (M : systemLevel R n),
      (transport (a.app (op l))).map
          (((systemTensorCoherence A).ordinaryAssoc R h k).hom.app M) ≫
          (quotient (h.trans k)).ordinary.hom.app M =
        (quotient h).ordinary.hom.app ((systemTensor A R k).obj M) ≫
          (systemTensor A S h).map ((quotient k).ordinary.hom.app M) ≫
          ((systemTensorCoherence A).ordinaryAssoc S h k).hom.app
            ((transport (a.app (op n))).obj M)) ∧
    (∀ (n : ℕ) (M : DerivedCategory (systemLevel R n)),
      (transport (a.app (op n))).mapDerivedCategory.map
          (((systemTensorCoherence A).derivedUnit R n).hom.app M) =
        (quotient (Nat.le_refl n)).derived.hom.app M ≫
          ((systemTensorCoherence A).derivedUnit S n).hom.app
            ((transport (a.app (op n))).mapDerivedCategory.obj M)) ∧
    (∀ {l m n : ℕ} (h : l ≤ m) (k : m ≤ n)
      (M : DerivedCategory (systemLevel R n)),
      (transport (a.app (op l))).mapDerivedCategory.map
          (((systemTensorCoherence A).derivedAssoc R h k).hom.app M) ≫
          (quotient (h.trans k)).derived.hom.app M =
        (quotient h).derived.hom.app ((systemDerivedTensor A R k).obj M) ≫
          (systemDerivedTensor A S h).map ((quotient k).derived.hom.app M) ≫
          ((systemTensorCoherence A).derivedAssoc S h k).hom.app
            ((transport (a.app (op n))).mapDerivedCategory.obj M)) ∧
    (∀ (n : ℕ) (M : DerivedCategory (StrictRingSystem R)),
      adjointTransition A R (Nat.le_refl n) M =
        ((systemTensorCoherence A).derivedUnit R n).hom.app ((derivedSystemEvaluation R n).obj M)) ∧
    (∀ (n : ℕ) (M : DerivedCategory (StrictRingSystem S)),
      adjointTransition A S (Nat.le_refl n) M =
        ((systemTensorCoherence A).derivedUnit S n).hom.app ((derivedSystemEvaluation S n).obj M)) ∧
    (∀ {l m n : ℕ} (h : l ≤ m) (k : m ≤ n)
      (M : DerivedCategory (StrictRingSystem R)),
      ((systemTensorCoherence A).derivedAssoc R h k).inv.app ((derivedSystemEvaluation R n).obj M) ≫
          (systemDerivedTensor A R h).map (adjointTransition A R k M) ≫
          adjointTransition A R h M = adjointTransition A R (h.trans k) M) ∧
    (∀ {l m n : ℕ} (h : l ≤ m) (k : m ≤ n)
      (M : DerivedCategory (StrictRingSystem S)),
      ((systemTensorCoherence A).derivedAssoc S h k).inv.app ((derivedSystemEvaluation S n).obj M) ≫
          (systemDerivedTensor A S h).map (adjointTransition A S k M) ≫
          adjointTransition A S h M = adjointTransition A S (h.trans k) M) ∧
    (∀ (M : DerivedCategory (StrictRingSystem R)) {m n : ℕ} (h : m ≤ n),
      (quotient h).derived.inv.app ((derivedSystemEvaluation R n).obj M) ≫
          (transport (a.app (op m))).mapDerivedCategory.map (adjointTransition A R h M) ≫
          (derivedLevel m).inv.app M =
        (systemDerivedTensor A S h).map ((derivedLevel n).inv.app M) ≫
          adjointTransition A S h (derivedEquivalence.functor.obj M)) ∧
    (∀ (M : DerivedCategory (StrictRingSystem R)),
      (∀ (m n : ℕ) (h : m ≤ n), IsIso (adjointTransition A R h M)) ↔
        ∀ (m n : ℕ) (h : m ≤ n),
          IsIso (adjointTransition A S h (derivedEquivalence.functor.obj M)))

/-- Complete strict-system coefficient transport, including the normalization of
localization, reduction and every adjoint transition.
Source: def-pur-section-invariant, finite-clopen expansion; Stacks 03D7 and 015F
(blueprint: lem-pur-ring-iso-quotient-system-transport). -/
abbrev CoherentTransport (R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (a : R ≅ S)
    (c : Cone R) (d : Cone S) (e : c.pt ≅ d.pt)
    (A : SystemScalarAssignment (J := J)) :=
  TransportComparisonData
    (StrictRingSystem R ≌ StrictRingSystem S)
    (fun equivalence ↦
      equivalence.functor.Additive)
    (fun equivalence ↦
      PreservesFiniteLimits equivalence.functor)
    (fun equivalence ↦
      PreservesFiniteColimits equivalence.functor)
    (DerivedCategory (StrictRingSystem R) ≌ DerivedCategory (StrictRingSystem S))
    (fun equivalence additive derivedEquivalence ↦
      letI := additive; DerivedCategory.Q ⋙ derivedEquivalence.functor ≅
    equivalence.functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (fun equivalence ↦
      ∀ n : ℕ, equivalence.functor ⋙ systemEvaluation S n ≅
    systemEvaluation R n ⋙ transport (a.app (op n)))
    (fun derivedEquivalence ↦
      ∀ n : ℕ, derivedEquivalence.functor ⋙ derivedSystemEvaluation S n ≅
    derivedSystemEvaluation R n ⋙ (transport (a.app (op n))).mapDerivedCategory)
    (Reduction R c A)
    (Reduction S d A)
    (fun equivalence reductionR reductionS ↦
      reductionR.ordinary ⋙ equivalence.functor ≅ transport e ⋙ reductionS.ordinary)
    (fun derivedEquivalence reductionR reductionS ↦
      reductionR.derived ⋙ derivedEquivalence.functor ≅
    (transport e).mapDerivedCategory ⋙ reductionS.derived)
    (∀ n : ℕ, ScalarSquare (c.π.app (op n)) (d.π.app (op n)) e (a.app (op n))
    (A (c.π.app (op n))) (A (d.π.app (op n))))
    (∀ {m n : ℕ} (h : m ≤ n),
    ScalarSquare (R.map (homOfLE h).op) (S.map (homOfLE h).op)
      (a.app (op n)) (a.app (op m))
      (A (R.map (homOfLE h).op)) (A (S.map (homOfLE h).op)))
    (fun equivalence additive limits colimits derivedEquivalence localization level derivedLevel
      reductionR reductionS reduction derivedReduction projection quotient ↦
      CoherentTransportConditions R S a c d e A (additive := additive) (limits := limits)
        (colimits := colimits) equivalence derivedEquivalence localization level derivedLevel
        reductionR reductionS reduction derivedReduction projection quotient)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard derivedSquare systemModelTmul
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso
  DerivedCategory.Q DerivedCategory.Qh DerivedCategory.quotientCompQhIso

private theorem derivedSquare_eq {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (ρ : restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) ⋙
        transport e ≅ transport e' ⋙
          restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)) :
    derivedSquare a b e e' ρ = Functor.mapDerivedCategorySquareIso ρ := by
  unfold derivedSquare
  rfl

private def scalarRestrictionSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom) :
    restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) ⋙
        transport e ≅ transport e' ⋙
          restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b) := by
  have h' : e.inv ≫ a = b ≫ e'.inv := by
    apply (cancel_epi e.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [h]
    simp
  exact systemScalarRestrictionComposition e.inv a (e.inv ≫ a) rfl ≪≫
    (systemScalarRestrictionComposition b e'.inv (e.inv ≫ a) h').symm

private def strictTransportTransition
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S)
    (M : StrictRingSystem R) {m n : ℕ} (h : m ≤ n) :
    (transport (a.app (op n))).obj (M.level n) ⟶
      (systemRestriction S h).obj ((transport (a.app (op m))).obj (M.level m)) :=
  (transport (a.app (op n))).map (M.transition h) ≫
    (scalarRestrictionSquare _ _ _ _ (a.hom.naturality (homOfLE h).op).symm).hom.app
      (M.level m)

private def strictTransportObj
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S)
    (M : StrictRingSystem R) : StrictRingSystem S where
  level n := (transport (a.app (op n))).obj (M.level n)
  transition h := strictTransportTransition a M h
  identity := M.identity
  compose := M.compose

private def strictTransportMap
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S)
    {M N : StrictRingSystem R} (f : M ⟶ N) :
    strictTransportObj a M ⟶ strictTransportObj a N where
  app n := (transport (a.app (op n))).map (f.app n)
  comm := by
    intro m n h
    ext U x
    exact congrArg (fun g ↦ g.val.app U x) (f.comm h)

private def strictTransportFunctor
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    StrictRingSystem R ⥤ StrictRingSystem S where
  obj := strictTransportObj a
  map := strictTransportMap a
  map_id M := by
    apply strictRingSystem_hom_ext
    intro n
    exact (transport (a.app (op n))).map_id _
  map_comp f g := by
    apply strictRingSystem_hom_ext
    intro n
    exact (transport (a.app (op n))).map_comp _ _

private def transportInverse {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    transport a ⋙ transport a.symm ≅ 𝟭 (Modules R) :=
  systemScalarRestrictionComposition a.hom a.inv (𝟙 R) (by simp) ≪≫
    systemScalarRestrictionUnit (𝟙 R) rfl

private def strictTransportInverseHom
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S)
    (M : StrictRingSystem R) :
    (strictTransportFunctor a ⋙ strictTransportFunctor a.symm).obj M ⟶ M where
  app n := (transportInverse (a.app (op n))).hom.app (M.level n)
  comm := by
    intro m n h
    ext U x
    rfl

private def strictTransportInverseInv
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S)
    (M : StrictRingSystem R) :
    M ⟶ (strictTransportFunctor a ⋙ strictTransportFunctor a.symm).obj M where
  app n := (transportInverse (a.app (op n))).inv.app (M.level n)
  comm := by
    intro m n h
    ext U x
    rfl

private def strictTransportInverseIso
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    strictTransportFunctor a ⋙ strictTransportFunctor a.symm ≅ 𝟭 (StrictRingSystem R) :=
  NatIso.ofComponents (fun M ↦ {
    hom := strictTransportInverseHom a M
    inv := strictTransportInverseInv a M
    hom_inv_id := by
      apply strictRingSystem_hom_ext
      intro n
      exact (transportInverse (a.app (op n))).hom_inv_id_app (M.level n)
    inv_hom_id := by
      apply strictRingSystem_hom_ext
      intro n
      exact (transportInverse (a.app (op n))).inv_hom_id_app (M.level n) }) (by
    intro M N f
    apply strictRingSystem_hom_ext
    intro n
    ext U x
    rfl)

private def strictTransportEquivalence
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    StrictRingSystem R ≌ StrictRingSystem S where
  functor := strictTransportFunctor a
  inverse := strictTransportFunctor a.symm
  unitIso := (strictTransportInverseIso a).symm
  counitIso := strictTransportInverseIso a.symm
  functor_unitIso_comp := by
    intro M
    apply strictRingSystem_hom_ext
    intro n
    ext U x
    rfl


private instance strictTransportIsEquivalence
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    (strictTransportFunctor a).IsEquivalence :=
  (strictTransportEquivalence a).isEquivalence_functor

private instance strictTransportAdditive
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    (strictTransportFunctor a).Additive where
  map_add := by
    intro M N f g
    apply strictRingSystem_hom_ext
    intro n
    change (transport (a.app (op n))).map ((f + g).app n) = _
    have h (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (P Q : StrictRingSystem B)
        (s t : P ⟶ Q) : (s + t).app n = s.app n + t.app n :=
      (systemEvaluation B n).map_add (f := s) (g := t)
    rw [h R M N f g, Functor.map_add]
    exact (h S _ _ ((strictTransportFunctor a).map f)
      ((strictTransportFunctor a).map g)).symm

private instance strictTransportEquivalenceAdditive
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    (strictTransportEquivalence a).functor.Additive := by
  change (strictTransportFunctor a).Additive
  infer_instance

private instance strictTransportLimits
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    PreservesFiniteLimits (strictTransportFunctor a) := inferInstance

private instance strictTransportColimits
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    PreservesFiniteColimits (strictTransportFunctor a) := inferInstance

private def strictTransportLevel
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S) (n : ℕ) :
    strictTransportFunctor a ⋙ systemEvaluation S n ≅
      systemEvaluation R n ⋙ transport (a.app (op n)) := Iso.refl _

private theorem strictTransport_level
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S)
    (M : StrictRingSystem R) (n : ℕ) :
    ((strictTransportFunctor a).obj M).level n =
      (transport (a.app (op n))).obj (M.level n) := rfl

private theorem strictTransport_transition
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S)
    (M : StrictRingSystem R) {m n : ℕ} (h : m ≤ n) (U : Cᵒᵖ) :
    HEq (fun x ↦ (((strictTransportFunctor a).obj M).transition h).val.app U x)
      (fun x ↦ (M.transition h).val.app U x) := HEq.rfl

private theorem strictTransport_map
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S)
    {M N : StrictRingSystem R} (f : M ⟶ N) (n : ℕ) (U : Cᵒᵖ) :
    HEq (fun x ↦ (((strictTransportFunctor a).map f).app n).val.app U x)
      (fun x ↦ (f.app n).val.app U x) := HEq.rfl

private theorem strictTransport_level_sections
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S)
    (n : ℕ) (M : StrictRingSystem R) (U : Cᵒᵖ) (x : (M.level n).val.obj U) :
    HEq (((strictTransportLevel a n).inv.app M).val.app U x) x := HEq.rfl

attribute [local irreducible] strictTransportFunctor

private def scalarTransportEquivalence {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    Modules R ≌ Modules S where
  functor := transport a
  inverse := transport a.symm
  unitIso := (transportInverse a).symm
  counitIso := transportInverse a.symm
  functor_unitIso_comp := by
    intro M
    ext U x
    rfl


private instance scalarTransportEquivalenceAdditive
    {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    (scalarTransportEquivalence a).functor.Additive := by
  change (transport a).Additive
  infer_instance

private theorem normalizedComparison_exists
    {A₀ B₀ C₀ D₀ : Type*} [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    {L : A₀ ⥤ B₀} {U : B₀ ⥤ A₀} {L' : C₀ ⥤ D₀} {U' : D₀ ⥤ C₀}
    (a : L ⊣ U) (b : L' ⊣ U') (G : A₀ ⥤ C₀) (H : B₀ ⥤ D₀)
    [G.IsEquivalence] [H.IsEquivalence] (ρ : U ⋙ G ≅ H ⋙ U') :
    ∃! j : L ⋙ H ≅ G ⋙ L', (mateEquiv a b j.inv).natTrans = ρ.hom := by
  obtain ⟨j, hj, hu, _⟩ := exists_equivalenceAdjunctionComparison
    G.asEquivalence H.asEquivalence a b ρ
  exact ⟨j, hj, hu⟩

private def normalizedComparison
    {A₀ B₀ C₀ D₀ : Type*} [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    {L : A₀ ⥤ B₀} {U : B₀ ⥤ A₀} {L' : C₀ ⥤ D₀} {U' : D₀ ⥤ C₀}
    (a : L ⊣ U) (b : L' ⊣ U') (G : A₀ ⥤ C₀) (H : B₀ ⥤ D₀)
    [G.IsEquivalence] [H.IsEquivalence] (ρ : U ⋙ G ≅ H ⋙ U') :
    L ⋙ H ≅ G ⋙ L' :=
  (normalizedComparison_exists a b G H ρ).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedComparison_inv
    {A₀ B₀ C₀ D₀ : Type*} [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    {L : A₀ ⥤ B₀} {U : B₀ ⥤ A₀} {L' : C₀ ⥤ D₀} {U' : D₀ ⥤ C₀}
    (a : L ⊣ U) (b : L' ⊣ U') (G : A₀ ⥤ C₀) (H : B₀ ⥤ D₀)
    [G.IsEquivalence] [H.IsEquivalence] (ρ : U ⋙ G ≅ H ⋙ U') :
    (normalizedComparison a b G H ρ).inv = ((mateEquiv a b).symm ρ.hom).natTrans := by
  have hm := (normalizedComparison_exists a b G H ρ).exists.choose_spec
  change mateEquiv a b (normalizedComparison a b G H ρ).inv = ρ.hom at hm
  have he := congrArg (mateEquiv a b).symm hm
  simpa only [Equiv.symm_apply_apply] using congrArg TwoSquare.natTrans he

private instance transportIsEquivalence {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    (transport a).IsEquivalence := (scalarTransportEquivalence a).isEquivalence_functor

private instance transportDerivedEquivalence {R S : Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    (transport a).mapDerivedCategory.IsEquivalence :=
  Functor.isEquivalence_mapDerivedCategory _

private instance strictTransportDerivedEquivalence
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    (strictTransportFunctor a).mapDerivedCategory.IsEquivalence :=
  Functor.isEquivalence_mapDerivedCategory _

private def ordinaryScalarSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b) :
    A.model.E ⋙ transport e' ≅ transport e ⋙ B.model.E :=
  normalizedComparison A.ordinaryAdj B.ordinaryAdj (transport e)
    (transport e') (scalarRestrictionSquare a b e e' h)

private theorem transportedTensorHomExt {R R' S : Sheaf J CommRingCat.{w}}
    {φ : R ⟶ R'} (A : SystemScalarModel φ) (e : R' ≅ S)
    (M : Modules R) (N : Modules S)
    (f g : (transport e).obj (A.model.E.obj M) ⟶ N)
    (h : ∀ U x, f.val.app U (systemModelTmul A.model M U 1 x) =
      g.val.app U (systemModelTmul A.model M U 1 x)) : f = g := by
  let j := (transportInverse e).inv.app (A.model.E.obj M)
  have he : j ≫ (transport e.symm).map f = j ≫ (transport e.symm).map g := by
    apply systemScalarModel_hom_ext A M ((transport e.symm).obj N)
    intro U x
    change f.val.app U (systemModelTmul A.model M U 1 x) =
      g.val.app U (systemModelTmul A.model M U 1 x)
    exact h U x
  have he' := (cancel_epi j).1 he
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact congrArg (fun f ↦ f.val.app U x) he'

set_option backward.defeqAttrib.useBackward true in
private theorem conjugateLeftAdjointUniq
    {D E : Type*} [Category D] [Category E]
    {L₁ L₂ : D ⥤ E} {R₁ R₂ : E ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (e : R₁ ≅ R₂) :
    conjugateEquiv a₁ a₂ ((a₁.ofNatIsoRight e).leftAdjointUniq a₂).inv = e.hom := by
  ext X
  rw [conjugateEquiv_apply_app, Adjunction.leftAdjointUniq_inv_app,
    ← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app]
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [Category.assoc, ← e.hom.naturality, ← Category.assoc,
    a₁.right_triangle_components, Category.id_comp]

private theorem conjugateLeftAdjointUniqHom
    {D E : Type*} [Category D] [Category E]
    {L₁ L₂ : D ⥤ E} {R₁ R₂ : E ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (e : R₁ ≅ R₂) :
    conjugateEquiv a₂ a₁ ((a₁.ofNatIsoRight e).leftAdjointUniq a₂).hom = e.inv := by
  apply (cancel_mono e.hom).1
  conv_rhs => rw [Iso.inv_hom_id]
  rw [← conjugateLeftAdjointUniq a₁ a₂ e]
  exact conjugateEquiv_comm a₂ a₁ (by simp)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryScalarSquare_inv {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b) :
    (ordinaryScalarSquare a b e e' h A B).inv =
      ((mateEquiv A.ordinaryAdj B.ordinaryAdj).symm
        (scalarRestrictionSquare a b e e' h).hom).natTrans :=
  normalizedComparison_inv A.ordinaryAdj B.ordinaryAdj _ _ _

private theorem ordinaryScalarSquare_transpose {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b)
    (M : Modules R) (N : Modules R') (f : A.model.E.obj M ⟶ N) :
    B.ordinaryAdj.homEquiv _ _
        ((ordinaryScalarSquare a b e e' h A B).inv.app M ≫ (transport e').map f) =
      (transport e).map (A.ordinaryAdj.homEquiv _ _ f) ≫
        (scalarRestrictionSquare a b e e' h).hom.app N := by
  rw [ordinaryScalarSquare_inv]
  exact adjunctionMate_transpose A.ordinaryAdj B.ordinaryAdj
    (scalarRestrictionSquare a b e e' h).hom M N f

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryScalarSquare_tmul {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b)
    (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) (r : R'.obj.obj U) :
    ((ordinaryScalarSquare a b e e' h A B).hom.app M).val.app U
        (systemModelTmul A.model M U r x) =
      systemModelTmul B.model ((transport e).obj M) U (e'.hom.hom.app U r) x := by
  let ι := ordinaryScalarSquare a b e e' h A B
  let ρ := scalarRestrictionSquare a b e e' h
  have hu := unit_mateEquiv_symm A.ordinaryAdj B.ordinaryAdj ρ.hom M
  change (transport e).map (A.ordinaryAdj.unit.app M) ≫ ρ.hom.app (A.model.E.obj M) =
    B.ordinaryAdj.unit.app ((transport e).obj M) ≫
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)).map
        ((((mateEquiv A.ordinaryAdj B.ordinaryAdj).symm
          (scalarRestrictionSquare a b e e' h).hom).natTrans).app M) at hu
  rw [← ordinaryScalarSquare_inv a b e e' h A B] at hu
  change (transport e).map (A.ordinaryAdj.unit.app M) ≫ ρ.hom.app (A.model.E.obj M) =
    B.ordinaryAdj.unit.app ((transport e).obj M) ≫
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)).map
        (ι.inv.app M) at hu
  have hunit :
      (transport e).map (A.ordinaryAdj.unit.app M) ≫ ρ.hom.app (A.model.E.obj M) ≫
        (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)).map
          (ι.hom.app M) = B.ordinaryAdj.unit.app ((transport e).obj M) := by
    rw [← Category.assoc, hu, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app]
    erw [(restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map b)).map_id, Category.comp_id]
  have hx := congrArg (fun f ↦ f.val.app U x) hunit
  change (ι.hom.app M).val.app U ((A.ordinaryAdj.unit.app M).val.app U x) =
    (B.ordinaryAdj.unit.app ((transport e).obj M)).val.app U x at hx
  rw [A.unit_normalized, B.unit_normalized] at hx
  have he : e'.inv.hom.app U (e'.hom.hom.app U r) = r :=
    congrArg (fun f ↦ f.hom.app U r) e'.hom_inv_id
  have hs := ((ι.hom.app M).val.app U).hom.map_smul (e'.hom.hom.app U r)
    (systemModelTmul A.model M U 1 x)
  change (ι.hom.app M).val.app U
      ((e'.inv.hom.app U (e'.hom.hom.app U r)) •
        (show (A.model.E.obj M).val.obj U from systemModelTmul A.model M U 1 x)) = _ at hs
  rw [he] at hs
  change (ι.hom.app M).val.app U _ = _
  have hx' : (ι.hom.app M).val.app U
      (systemModelTmul A.model M U 1 x) =
        systemModelTmul B.model ((transport e).obj M) U 1 x := hx
  change (ι.hom.app M).val.app U
      (r • (show (A.model.E.obj M).val.obj U from systemModelTmul A.model M U 1 x)) =
    (e'.hom.hom.app U r) • (show (B.model.E.obj ((transport e).obj M)).val.obj U from
      (ι.hom.app M).val.app U (systemModelTmul A.model M U 1 x)) at hs
  rw [hx'] at hs
  simpa only [systemModelTmul, one_smul] using hs


private theorem ordinaryScalarSquare_mate {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b) :
    (mateEquiv A.ordinaryAdj B.ordinaryAdj
      (ordinaryScalarSquare a b e e' h A B).inv).natTrans =
        (scalarRestrictionSquare a b e e' h).hom  := by
  rw [ordinaryScalarSquare_inv]
  exact congrArg TwoSquare.natTrans ((mateEquiv _ _).apply_symm_apply _)


attribute [local irreducible] ordinaryScalarSquare

private theorem ordinaryScalarSquare_one {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b)
    (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((ordinaryScalarSquare a b e e' h A B).hom.app M).val.app U
      (systemModelTmul A.model M U 1 x) =
    systemModelTmul B.model ((transport e).obj M) U 1 x := by
  have he : e'.hom.hom.app U (1 : R'.obj.obj U) = 1 := map_one _
  exact (ordinaryScalarSquare_tmul a b e e' h A B M U x 1).trans
    (congrArg (fun r ↦ systemModelTmul B.model ((transport e).obj M) U r x) he)

private def derivedScalarSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b) :
    A.model.T ⋙ (transport e').mapDerivedCategory ≅
      (transport e).mapDerivedCategory ⋙ B.model.T :=
  normalizedComparison A.adjunction B.adjunction (transport e).mapDerivedCategory
    (transport e').mapDerivedCategory (derivedSquare a b e e' (scalarRestrictionSquare a b e e' h))

private theorem invertComparisonForward
    {D : Type*} [Category D] {W X Y Z U V : D} (α : W ≅ X) (β : Y ≅ Z)
    (f₁ : W ⟶ U) (f₂ : U ⟶ Y) (g₁ : X ⟶ V) (g₂ : V ⟶ Z)
    (h : α.inv ≫ f₁ ≫ f₂ = g₁ ≫ g₂ ≫ β.inv) :
    α.hom ≫ g₁ ≫ g₂ = f₁ ≫ f₂ ≫ β.hom := by
  apply (cancel_epi α.inv).1
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [Category.assoc α.inv f₁ f₂, h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedScalarSquare_inv {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b) :
    (derivedScalarSquare a b e e' h A B).inv =
      ((mateEquiv A.adjunction B.adjunction).symm
        (derivedSquare a b e e' (scalarRestrictionSquare a b e e' h)).hom).natTrans :=
  normalizedComparison_inv A.adjunction B.adjunction _ _ _

private theorem derivedScalarSquare_mate {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b) :
    (mateEquiv A.adjunction B.adjunction
      (derivedScalarSquare a b e e' h A B).inv).natTrans =
        (derivedSquare a b e e' (scalarRestrictionSquare a b e e' h)).hom := by
  rw [derivedScalarSquare_inv]
  exact congrArg TwoSquare.natTrans ((mateEquiv _ _).apply_symm_apply _)

private theorem derivedScalarSquare_transpose {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b)
    (M : DerivedCategory (Modules R)) (N : DerivedCategory (Modules R'))
    (f : A.model.T.obj M ⟶ N) :
    B.adjunction.homEquiv _ _
        ((derivedScalarSquare a b e e' h A B).inv.app M ≫
          (transport e').mapDerivedCategory.map f) =
      (transport e).mapDerivedCategory.map (A.adjunction.homEquiv _ _ f) ≫
        (derivedSquare a b e e' (scalarRestrictionSquare a b e e' h)).hom.app N := by
  rw [derivedScalarSquare_inv]
  exact adjunctionMate_transpose A.adjunction B.adjunction
    (derivedSquare a b e e' (scalarRestrictionSquare a b e e' h)).hom M N f

attribute [local irreducible] derivedScalarSquare

private theorem derivedMate_isoComparison
    {A₀ B₀ C₀ D₀ A₁ B₁ C₁ D₁ : Type*}
    [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    [Category A₁] [Category B₁] [Category C₁] [Category D₁]
    {L : A₀ ⥤ B₀} {R : B₀ ⥤ A₀} {L' : C₀ ⥤ D₀} {R' : D₀ ⥤ C₀}
    {LD : A₁ ⥤ B₁} {RD : B₁ ⥤ A₁} {LD' : C₁ ⥤ D₁} {RD' : D₁ ⥤ C₁}
    {G : A₀ ⥤ C₀} {H : B₀ ⥤ D₀} {GD : A₁ ⥤ C₁} {HD : B₁ ⥤ D₁}
    {QA : A₀ ⥤ A₁} {QB : B₀ ⥤ B₁} {QC : C₀ ⥤ C₁} {QD : D₀ ⥤ D₁}
    (a : L ⊣ R) (b : L' ⊣ R') (ad : LD ⊣ RD) (bd : LD' ⊣ RD')
    (ε : QA ⋙ LD ⟶ L ⋙ QB) (ε' : QC ⋙ LD' ⟶ L' ⋙ QD)
    (ρ : QB ⋙ RD ≅ R ⋙ QA) (ρ' : QD ⋙ RD' ≅ R' ⋙ QC)
    (γ : QA ⋙ GD ≅ G ⋙ QC) (η : QB ⋙ HD ≅ H ⋙ QD)
    (ha : ∀ P K (f : L.obj P ⟶ K),
      ad.homEquiv _ _ (ε.app P ≫ QB.map f) = QA.map (a.homEquiv _ _ f) ≫ ρ.inv.app K)
    (hb : ∀ P K (f : L'.obj P ⟶ K),
      bd.homEquiv _ _ (ε'.app P ≫ QD.map f) = QC.map (b.homEquiv _ _ f) ≫ ρ'.inv.app K)
    (τ : R ⋙ G ⟶ H ⋙ R') (τD : RD ⋙ GD ⟶ HD ⋙ RD')
    (hτ : ∀ K, τD.app (QB.obj K) ≫ RD'.map (η.hom.app K) ≫ ρ'.hom.app (H.obj K) =
      GD.map (ρ.hom.app K) ≫ γ.hom.app (R.obj K) ≫ QC.map (τ.app K))
    (i : L ⋙ H ≅ G ⋙ L') (j : LD ⋙ HD ≅ GD ⋙ LD')
    (hi : ∀ P, b.homEquiv _ _ (i.inv.app P) = G.map (a.unit.app P) ≫ τ.app (L.obj P))
    (hj : j.inv = ((mateEquiv ad bd).symm τD).natTrans) (P : A₀) :
    j.hom.app (QA.obj P) ≫ LD'.map (γ.hom.app P) ≫ ε'.app (G.obj P) =
      HD.map (ε.app P) ≫ η.hom.app (L.obj P) ≫ QD.map (i.hom.app P) := by
  have ht := derivedMate_comparison a b ad bd ε ε' ρ ρ' γ η ha hb τ τD hτ i.inv hi P
  change ((mateEquiv ad bd).symm τD).natTrans.app _ ≫ _ ≫ _ = _ at ht
  rw [← hj] at ht
  exact invertComparisonForward (j.app (QA.obj P)) (QD.mapIso (i.app P)) _ _ _ _ ht

private theorem cochainMateUnit
    {A₀ B₀ C₀ D₀ : Type*} [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    [Preadditive A₀] [Preadditive B₀] [Preadditive C₀] [Preadditive D₀]
    {L : A₀ ⥤ B₀} {R : B₀ ⥤ A₀} {L' : C₀ ⥤ D₀} {R' : D₀ ⥤ C₀}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
    (a : L ⊣ R) (b : L' ⊣ R') (G : A₀ ⥤ C₀) (H : B₀ ⥤ D₀)
    [G.Additive] [H.Additive] (i : L ⋙ H ≅ G ⋙ L') (τ : R ⋙ G ⟶ H ⋙ R')
    (hi : ∀ P, b.homEquiv _ _ (i.inv.app P) = G.map (a.unit.app P) ≫ τ.app (L.obj P))
    (K : CochainComplex A₀ ℤ) :
    (b.mapHomologicalComplex (.up ℤ)).homEquiv
        ((G.mapHomologicalComplex (.up ℤ)).obj K)
        ((H.mapHomologicalComplex (.up ℤ)).obj ((L.mapHomologicalComplex (.up ℤ)).obj K))
        ((NatIso.mapHomologicalComplex i (.up ℤ)).inv.app K) =
      (G.mapHomologicalComplex (.up ℤ)).map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        (τ.mapHomologicalComplex (.up ℤ)).app ((L.mapHomologicalComplex (.up ℤ)).obj K) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact hi (K.X n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryScalarSquare_unit {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b) (M : Modules R) :
    B.ordinaryAdj.homEquiv _ _ ((ordinaryScalarSquare a b e e' h A B).inv.app M) =
      (transport e).map (A.ordinaryAdj.unit.app M) ≫
        (scalarRestrictionSquare a b e e' h).hom.app (A.model.E.obj M) := by
  have ht := ordinaryScalarSquare_transpose a b e e' h A B M (A.model.E.obj M) (𝟙 _)
  erw [(transport e').map_id] at ht
  erw [Category.comp_id] at ht
  dsimp only [Functor.comp_obj]
  simpa only [Adjunction.homEquiv_id] using ht

private theorem derivedMate_cochainIsoComparison
    {A₀ B₀ C₀ D₀ : Type*} [Category A₀] [Category B₀] [Category C₀] [Category D₀]
    [Abelian A₀] [Abelian B₀] [Abelian C₀] [Abelian D₀]
    [HasDerivedCategory A₀] [HasDerivedCategory B₀]
    [HasDerivedCategory C₀] [HasDerivedCategory D₀]
    {L : A₀ ⥤ B₀} {R : B₀ ⥤ A₀} {L' : C₀ ⥤ D₀} {R' : D₀ ⥤ C₀}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
    (a : L ⊣ R) (b : L' ⊣ R') (G : A₀ ⥤ C₀) (H : B₀ ⥤ D₀)
    [G.Additive] [H.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    {T : DerivedCategory A₀ ⥤ DerivedCategory B₀}
    {T' : DerivedCategory C₀ ⥤ DerivedCategory D₀}
    (ad : T ⊣ R.mapDerivedCategory) (bd : T' ⊣ R'.mapDerivedCategory)
    (ε : DerivedCategory.Q ⋙ T ⟶ L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ε' : DerivedCategory.Q ⋙ T' ⟶ L'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ha : ∀ P K (f : (L.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      ad.homEquiv _ _ (ε.app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
          R.mapDerivedCategoryFactors.inv.app K)
    (hb : ∀ P K (f : (L'.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      bd.homEquiv _ _ (ε'.app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((b.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
          R'.mapDerivedCategoryFactors.inv.app K)
    (ρ : R ⋙ G ≅ H ⋙ R') (i : L ⋙ H ≅ G ⋙ L')
    (j : T ⋙ H.mapDerivedCategory ≅ G.mapDerivedCategory ⋙ T')
    (hi : ∀ P, b.homEquiv _ _ (i.inv.app P) = G.map (a.unit.app P) ≫ ρ.hom.app (L.obj P))
    (hj : j.inv = ((mateEquiv ad bd).symm (Functor.mapDerivedCategorySquareIso ρ).hom).natTrans)
    (P : CochainComplex A₀ ℤ) :
    j.hom.app (DerivedCategory.Q.obj P) ≫ T'.map (G.mapDerivedCategoryFactors.hom.app P) ≫
        ε'.app ((G.mapHomologicalComplex (.up ℤ)).obj P) =
      H.mapDerivedCategory.map (ε.app P) ≫
        H.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex i (.up ℤ)).hom.app P) := by
  apply derivedMate_isoComparison (a.mapHomologicalComplex (.up ℤ))
    (b.mapHomologicalComplex (.up ℤ)) ad bd ε ε'
    R.mapDerivedCategoryFactors R'.mapDerivedCategoryFactors
    G.mapDerivedCategoryFactors H.mapDerivedCategoryFactors ha hb
    (ρ.hom.mapHomologicalComplex (.up ℤ)) (Functor.mapDerivedCategorySquareIso ρ).hom
    (Functor.exactSquare_fac ρ) (NatIso.mapHomologicalComplex i (.up ℤ)) j
    (cochainMateUnit a b G H i ρ.hom hi) hj P

private theorem derivedScalarSquare_rep {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b)
    (P : CochainComplex (Modules R) ℤ) :
    (derivedScalarSquare a b e e' h A B).hom.app (DerivedCategory.Q.obj P) ≫
        B.model.T.map ((transport e).mapDerivedCategoryFactors.hom.app P) ≫
        B.model.ε.app (((transport e).mapHomologicalComplex (.up ℤ)).obj P) =
      (transport e').mapDerivedCategory.map (A.model.ε.app P) ≫
        (transport e').mapDerivedCategoryFactors.hom.app
          ((A.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryScalarSquare a b e e' h A B)
            (.up ℤ)).hom.app P) := by
  exact derivedMate_cochainIsoComparison A.ordinaryAdj B.ordinaryAdj (transport e) (transport e')
    A.adjunction B.adjunction A.model.ε B.model.ε A.transpose B.transpose
    (scalarRestrictionSquare a b e e' h) (ordinaryScalarSquare a b e e' h A B)
    (derivedScalarSquare a b e e' h A B) (ordinaryScalarSquare_unit a b e e' h A B)
    (by rw [derivedScalarSquare_inv, derivedSquare_eq]) P

private def scalarSquare {R R' S S' : Sheaf J CommRingCat.{w}}
    (a : R ⟶ R') (b : S ⟶ S') (e : R ≅ S) (e' : R' ≅ S')
    (h : e.hom ≫ b = a ≫ e'.hom)
    (A : SystemScalarModel a) (B : SystemScalarModel b) :
    ScalarSquare a b e e' A B where
  restriction := scalarRestrictionSquare a b e e' h
  ordinary := ordinaryScalarSquare a b e e' h A B
  derived := derivedScalarSquare a b e e' h A B
  conditions := ⟨(by intro M U x; rfl),
    ordinaryScalarSquare_tmul a b e e' h A B,
    ordinaryScalarSquare_transpose a b e e' h A B,
    derivedScalarSquare_rep a b e e' h A B,
    derivedScalarSquare_transpose a b e e' h A B⟩

private theorem scalarOrdinaryAssoc
    {R₀ R₁ R₂ S₀ S₁ S₂ : Sheaf J CommRingCat.{w}}
    (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂) (fg : R₀ ⟶ R₂) (hfg : fg = f ≫ g)
    (f' : S₀ ⟶ S₁) (g' : S₁ ⟶ S₂) (fg' : S₀ ⟶ S₂) (hfg' : fg' = f' ≫ g')
    (e₀ : R₀ ≅ S₀) (e₁ : R₁ ≅ S₁) (e₂ : R₂ ≅ S₂)
    (hf : e₀.hom ≫ f' = f ≫ e₁.hom) (hg : e₁.hom ≫ g' = g ≫ e₂.hom)
    (hfgs : e₀.hom ≫ fg' = fg ≫ e₂.hom)
    (A : SystemScalarModel f) (B : SystemScalarModel g) (D : SystemScalarModel fg)
    (A' : SystemScalarModel f') (B' : SystemScalarModel g') (D' : SystemScalarModel fg')
    (M : Modules R₀) :
    (transport e₂).map ((systemScalarModelComposition hfg A B D).hom.app M) ≫
        (ordinaryScalarSquare fg fg' e₀ e₂ hfgs D D').hom.app M =
      (ordinaryScalarSquare g g' e₁ e₂ hg B B').hom.app (A.model.E.obj M) ≫
        B'.model.E.map ((ordinaryScalarSquare f f' e₀ e₁ hf A A').hom.app M) ≫
        (systemScalarModelComposition hfg' A' B' D').hom.app ((transport e₀).obj M) := by
  apply equivalenceAdjunctionComparison_compositor
    (scalarTransportEquivalence e₀) (scalarTransportEquivalence e₁)
    (scalarTransportEquivalence e₂)
    A.ordinaryAdj B.ordinaryAdj D.ordinaryAdj A'.ordinaryAdj B'.ordinaryAdj D'.ordinaryAdj
    (scalarRestrictionSquare f f' e₀ e₁ hf) (scalarRestrictionSquare g g' e₁ e₂ hg)
    (scalarRestrictionSquare fg fg' e₀ e₂ hfgs)
    (ordinaryScalarSquare f f' e₀ e₁ hf A A')
    (ordinaryScalarSquare g g' e₁ e₂ hg B B')
    (ordinaryScalarSquare fg fg' e₀ e₂ hfgs D D')
    (ordinaryScalarSquare_mate f f' e₀ e₁ hf A A')
    (ordinaryScalarSquare_mate g g' e₁ e₂ hg B B')
    (ordinaryScalarSquare_mate fg fg' e₀ e₂ hfgs D D')
    (systemScalarRestrictionComposition f g fg hfg)
    (systemScalarRestrictionComposition f' g' fg' hfg')
    (by intro N; ext U x; rfl)
    (systemScalarModelComposition hfg A B D) (systemScalarModelComposition hfg' A' B' D')
    (conjugateLeftAdjointUniqHom _ _ _) (conjugateLeftAdjointUniqHom _ _ _) M

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedRestrictionCompositionSquare
    {R₀ R₁ R₂ S₀ S₁ S₂ : Sheaf J CommRingCat.{w}}
    (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂) (fg : R₀ ⟶ R₂) (hfg : fg = f ≫ g)
    (f' : S₀ ⟶ S₁) (g' : S₁ ⟶ S₂) (fg' : S₀ ⟶ S₂) (hfg' : fg' = f' ≫ g')
    (e₀ : R₀ ≅ S₀) (e₁ : R₁ ≅ S₁) (e₂ : R₂ ≅ S₂)
    (hf : e₀.hom ≫ f' = f ≫ e₁.hom) (hg : e₁.hom ≫ g' = g ≫ e₂.hom)
    (hfgs : e₀.hom ≫ fg' = fg ≫ e₂.hom)
    (N : DerivedCategory (Modules R₂)) :
    (derivedSquare f f' e₀ e₁ (scalarRestrictionSquare f f' e₀ e₁ hf)).hom.app
        ((restrictScalars
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map g)).mapDerivedCategory.obj N) ≫
      (restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map f')).mapDerivedCategory.map
          ((derivedSquare g g' e₁ e₂ (scalarRestrictionSquare g g' e₁ e₂ hg)).hom.app N) ≫
      (Functor.exactDerivedRestrictionComposition _ _ _
        (systemScalarRestrictionComposition f' g' fg' hfg')).hom.app
          ((transport e₂).mapDerivedCategory.obj N) =
    (transport e₀).mapDerivedCategory.map
        ((Functor.exactDerivedRestrictionComposition _ _ _
          (systemScalarRestrictionComposition f g fg hfg)).hom.app N) ≫
      (derivedSquare fg fg' e₀ e₂ (scalarRestrictionSquare fg fg' e₀ e₂ hfgs)).hom.app N := by
  let res {X Y : Sheaf J CommRingCat.{w}} (q : X ⟶ Y) :=
    restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map q)
  have hd := Functor.mapDerivedCategorySquareIso_comp
    (res g) (res f) (res fg) (res g') (res f') (res fg')
    (transport e₂) (transport e₁) (transport e₀)
    (scalarRestrictionSquare g g' e₁ e₂ hg)
    (scalarRestrictionSquare f f' e₀ e₁ hf)
    (scalarRestrictionSquare fg fg' e₀ e₂ hfgs)
    (systemScalarRestrictionComposition f g fg hfg).symm
    (systemScalarRestrictionComposition f' g' fg' hfg').symm
    (by intro X; ext U x; rfl)
  have he := congrArg (fun q ↦ q.hom.app N) hd
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapDerivedCategoryNatIso_symm, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at he
  apply (cancel_epi ((transport e₀).mapDerivedCategory.map
    ((Functor.exactDerivedRestrictionComposition _ _ _
      (systemScalarRestrictionComposition f g fg hfg)).inv.app N))).1
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  apply (cancel_mono ((Functor.exactDerivedRestrictionComposition _ _ _
    (systemScalarRestrictionComposition f' g' fg' hfg')).inv.app
      ((transport e₂).mapDerivedCategory.obj N))).1
  simp only [Category.assoc, Iso.hom_inv_id_app]
  simp only [derivedSquare, Functor.exactDerivedRestrictionComposition,
    Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc, Iso.symm_hom]
  erw [Category.comp_id]
  simpa only [res, Category.assoc] using he

private theorem scalarDerivedAssoc
    {R₀ R₁ R₂ S₀ S₁ S₂ : Sheaf J CommRingCat.{w}}
    (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂) (fg : R₀ ⟶ R₂) (hfg : fg = f ≫ g)
    (f' : S₀ ⟶ S₁) (g' : S₁ ⟶ S₂) (fg' : S₀ ⟶ S₂) (hfg' : fg' = f' ≫ g')
    (e₀ : R₀ ≅ S₀) (e₁ : R₁ ≅ S₁) (e₂ : R₂ ≅ S₂)
    (hf : e₀.hom ≫ f' = f ≫ e₁.hom) (hg : e₁.hom ≫ g' = g ≫ e₂.hom)
    (hfgs : e₀.hom ≫ fg' = fg ≫ e₂.hom)
    (A : SystemScalarModel f) (B : SystemScalarModel g) (D : SystemScalarModel fg)
    (A' : SystemScalarModel f') (B' : SystemScalarModel g') (D' : SystemScalarModel fg')
    (M : DerivedCategory (Modules R₀)) :
    (transport e₂).mapDerivedCategory.map
        ((systemScalarModelDerivedComposition hfg A B D).hom.app M) ≫
        (derivedScalarSquare fg fg' e₀ e₂ hfgs D D').hom.app M =
      (derivedScalarSquare g g' e₁ e₂ hg B B').hom.app (A.model.T.obj M) ≫
        B'.model.T.map ((derivedScalarSquare f f' e₀ e₁ hf A A').hom.app M) ≫
        (systemScalarModelDerivedComposition hfg' A' B' D').hom.app
          ((transport e₀).mapDerivedCategory.obj M) := by
  apply equivalenceAdjunctionComparison_compositor
    (scalarTransportEquivalence e₀).mapDerivedCategory
    (scalarTransportEquivalence e₁).mapDerivedCategory
    (scalarTransportEquivalence e₂).mapDerivedCategory
    A.adjunction B.adjunction D.adjunction A'.adjunction B'.adjunction D'.adjunction
    (derivedSquare f f' e₀ e₁ (scalarRestrictionSquare f f' e₀ e₁ hf))
    (derivedSquare g g' e₁ e₂ (scalarRestrictionSquare g g' e₁ e₂ hg))
    (derivedSquare fg fg' e₀ e₂ (scalarRestrictionSquare fg fg' e₀ e₂ hfgs))
    (derivedScalarSquare f f' e₀ e₁ hf A A')
    (derivedScalarSquare g g' e₁ e₂ hg B B')
    (derivedScalarSquare fg fg' e₀ e₂ hfgs D D')
    (derivedScalarSquare_mate f f' e₀ e₁ hf A A')
    (derivedScalarSquare_mate g g' e₁ e₂ hg B B')
    (derivedScalarSquare_mate fg fg' e₀ e₂ hfgs D D')
    (Functor.exactDerivedRestrictionComposition _ _ _
      (systemScalarRestrictionComposition f g fg hfg))
    (Functor.exactDerivedRestrictionComposition _ _ _
      (systemScalarRestrictionComposition f' g' fg' hfg'))
    (by
      intro N
      exact derivedRestrictionCompositionSquare f g fg hfg f' g' fg' hfg'
        e₀ e₁ e₂ hf hg hfgs N)
    (systemScalarModelDerivedComposition hfg A B D)
    (systemScalarModelDerivedComposition hfg' A' B' D')
    (conjugateLeftAdjointUniqHom _ _ _) (conjugateLeftAdjointUniqHom _ _ _) M

private def reductionTransition (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (M : Modules c.pt) {m n : ℕ} (h : m ≤ n) :
    (A (c.π.app (op n))).model.E.obj M ⟶
      (systemRestriction B h).obj ((A (c.π.app (op m))).model.E.obj M) :=
  (A (B.map (homOfLE h).op)).ordinaryAdj.homEquiv _ _
    ((systemScalarModelComposition (c.w (homOfLE h).op).symm
      (A (c.π.app (op n))) (A (B.map (homOfLE h).op))
      (A (c.π.app (op m)))).hom.app M)

private theorem reductionTransition_tmul
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (M : Modules c.pt) {m n : ℕ} (h : m ≤ n)
    (U : Cᵒᵖ) (r : (B.obj (op n)).obj.obj U) (x : M.val.obj U) :
    (reductionTransition B c A M h).val.app U
        (systemModelTmul (A (c.π.app (op n))).model M U r x) =
      systemModelTmul (A (c.π.app (op m))).model M U
        ((B.map (homOfLE h).op).hom.app U r) x := by
  dsimp only [reductionTransition]
  rw [Adjunction.homEquiv_unit]
  change ((systemScalarModelComposition (c.w (homOfLE h).op).symm
      (A (c.π.app (op n))) (A (B.map (homOfLE h).op))
      (A (c.π.app (op m)))).hom.app M).val.app U
    (((A (B.map (homOfLE h).op)).ordinaryAdj.unit.app
      ((A (c.π.app (op n))).model.E.obj M)).val.app U _) = _
  rw [(A (B.map (homOfLE h).op)).unit_normalized]
  rw [systemScalarModelComposition_tmul]
  simp only [one_mul]

private theorem reductionTransition_one
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (M : Modules c.pt) {m n : ℕ} (h : m ≤ n)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    (reductionTransition B c A M h).val.app U
      (systemModelTmul (A (c.π.app (op n))).model M U 1 x) =
    systemModelTmul (A (c.π.app (op m))).model M U 1 x := by
  have he : (B.map (homOfLE h).op).hom.app U
      (1 : (B.obj (op n)).obj.obj U) = 1 := map_one _
  exact (reductionTransition_tmul B c A M h U 1 x).trans
    (congrArg (fun r ↦ systemModelTmul (A (c.π.app (op m))).model M U r x) he)

private def reductionObj (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (M : Modules c.pt) : StrictRingSystem B where
  level n := (A (c.π.app (op n))).model.E.obj M
  transition := reductionTransition B c A M
  identity := by
    intro n U x
    let η := systemScalarRestrictionUnit (B.map (homOfLE (Nat.le_refl n)).op)
      (B.map_id (op n))
    have he : reductionTransition B c A M (Nat.le_refl n) =
        η.inv.app ((A (c.π.app (op n))).model.E.obj M) := by
      apply systemScalarModel_hom_ext (A (c.π.app (op n)))
      intro V y
      change (reductionTransition B c A M (Nat.le_refl n)).val.app V _ =
        systemModelTmul (A (c.π.app (op n))).model M V 1 y
      simpa only [map_one] using
        reductionTransition_tmul B c A M (Nat.le_refl n) V 1 y
    exact congrArg (fun f ↦ f.val.app U x) he
  compose := by
    intro l m n h k U x
    have hc : B.map (homOfLE (h.trans k)).op =
        B.map (homOfLE k).op ≫ B.map (homOfLE h).op := by
      rw [← B.map_comp]
      rfl
    let η := systemScalarRestrictionComposition _ _ _ hc
    have he : reductionTransition B c A M (h.trans k) =
        reductionTransition B c A M k ≫
          (systemRestriction B k).map (reductionTransition B c A M h) ≫
          η.hom.app ((A (c.π.app (op l))).model.E.obj M) := by
      apply systemScalarModel_hom_ext (A (c.π.app (op n)))
      intro V y
      change (reductionTransition B c A M (h.trans k)).val.app V _ =
        (reductionTransition B c A M h).val.app V
          ((reductionTransition B c A M k).val.app V _)
      rw [reductionTransition_tmul, reductionTransition_tmul]
      simp only [map_one]
      rw [reductionTransition_tmul]
      simp only [map_one]
      rfl
    exact congrArg (fun f ↦ f.val.app U x) he

private def reductionMap (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) {M N : Modules c.pt} (f : M ⟶ N) :
    reductionObj B c A M ⟶ reductionObj B c A N where
  app n := (A (c.π.app (op n))).model.E.map f
  comm := by
    intro m n h
    apply systemScalarModel_hom_ext (A (c.π.app (op n)))
    intro U x
    change (reductionTransition B c A N h).val.app U
        (((A (c.π.app (op n))).model.E.map f).val.app U _) =
      ((A (c.π.app (op m))).model.E.map f).val.app U
        ((reductionTransition B c A M h).val.app U _)
    rw [systemScalarModel_map_tmul, reductionTransition_tmul,
      reductionTransition_tmul, systemScalarModel_map_tmul]

private def reductionFunctor (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) : Modules c.pt ⥤ StrictRingSystem B where
  obj := reductionObj B c A
  map := reductionMap B c A
  map_id M := by
    apply strictRingSystem_hom_ext
    intro n
    exact (A (c.π.app (op n))).model.E.map_id M
  map_comp f g := by
    apply strictRingSystem_hom_ext
    intro n
    exact (A (c.π.app (op n))).model.E.map_comp f g

private instance reductionFunctorAdditive
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) : (reductionFunctor B c A).Additive where
  map_add := by
    intro M N f g
    apply strictRingSystem_hom_ext
    intro n
    change (A (c.π.app (op n))).model.E.map (f + g) = _
    rw [Functor.map_add]
    exact ((systemEvaluation B n).map_add
      (f := (reductionFunctor B c A).map f) (g := (reductionFunctor B c A).map g)).symm

private def reductionEvaluation (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (n : ℕ) :
    reductionFunctor B c A ⋙ systemEvaluation B n ≅ (A (c.π.app (op n))).model.E :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N f
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

attribute [local semireducible] strictTransportFunctor in
private def reductionComparisonHom
    (R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (a : R ≅ S)
    (c : Cone R) (d : Cone S) (e : c.pt ≅ d.pt)
    (h : ∀ n, e.hom ≫ d.π.app (op n) = c.π.app (op n) ≫ (a.app (op n)).hom)
    (A : SystemScalarAssignment (J := J)) (M : Modules c.pt) :
    (reductionFunctor R c A ⋙ strictTransportFunctor a).obj M ⟶
      (transport e ⋙ reductionFunctor S d A).obj M where
  app n := (ordinaryScalarSquare _ _ e (a.app (op n)) (h n)
    (A (c.π.app (op n))) (A (d.π.app (op n)))).hom.app M
  comm := by
    intro m n k
    apply transportedTensorHomExt (A (c.π.app (op n))) (a.app (op n))
    intro U x
    change (reductionTransition S d A ((transport e).obj M) k).val.app U
        (((ordinaryScalarSquare _ _ e (a.app (op n)) (h n)
          (A (c.π.app (op n))) (A (d.π.app (op n)))).hom.app M).val.app U
          (systemModelTmul (A (c.π.app (op n))).model M U 1 x)) =
      ((ordinaryScalarSquare _ _ e (a.app (op m)) (h m)
        (A (c.π.app (op m))) (A (d.π.app (op m)))).hom.app M).val.app U
        ((reductionTransition R c A M k).val.app U
          (systemModelTmul (A (c.π.app (op n))).model M U 1 x))
    exact (congrArg ((reductionTransition S d A ((transport e).obj M) k).val.app U)
      (ordinaryScalarSquare_one _ _ e (a.app (op n)) (h n)
        (A (c.π.app (op n))) (A (d.π.app (op n))) M U x)).trans
      ((reductionTransition_one S d A ((transport e).obj M) k U x).trans
        ((ordinaryScalarSquare_one _ _ e (a.app (op m)) (h m)
          (A (c.π.app (op m))) (A (d.π.app (op m))) M U x).symm.trans
          (congrArg (((ordinaryScalarSquare _ _ e (a.app (op m)) (h m)
            (A (c.π.app (op m))) (A (d.π.app (op m)))).hom.app M).val.app U)
              (reductionTransition_one R c A M k U x).symm)))

attribute [local semireducible] strictTransportFunctor in
private def reductionComparison
    (R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (a : R ≅ S)
    (c : Cone R) (d : Cone S) (e : c.pt ≅ d.pt)
    (h : ∀ n, e.hom ≫ d.π.app (op n) = c.π.app (op n) ≫ (a.app (op n)).hom)
    (A : SystemScalarAssignment (J := J)) :
    reductionFunctor R c A ⋙ strictTransportFunctor a ≅ transport e ⋙ reductionFunctor S d A := by
  have hi (M : Modules c.pt) : IsIso (reductionComparisonHom R S a c d e h A M) := by
    apply (strictRingSystem_isIso_iff S _).2
    intro n
    change IsIso ((ordinaryScalarSquare _ _ e (a.app (op n)) (h n)
      (A (c.π.app (op n))) (A (d.π.app (op n)))).hom.app M)
    infer_instance
  exact NatIso.ofComponents (fun M ↦ by
    letI := hi M
    exact asIso (reductionComparisonHom R S a c d e h A M)) (by
    intro M N f
    apply strictRingSystem_hom_ext
    intro n
    exact (ordinaryScalarSquare _ _ e (a.app (op n)) (h n)
      (A (c.π.app (op n))) (A (d.π.app (op n)))).hom.naturality f)

attribute [local semireducible] strictTransportFunctor in
private theorem reductionComparison_tmul
    (R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (a : R ≅ S)
    (c : Cone R) (d : Cone S) (e : c.pt ≅ d.pt)
    (h : ∀ n, e.hom ≫ d.π.app (op n) = c.π.app (op n) ≫ (a.app (op n)).hom)
    (A : SystemScalarAssignment (J := J)) (M : Modules c.pt) (n : ℕ) (U : Cᵒᵖ)
    (r : (R.obj (op n)).obj.obj U) (x : M.val.obj U) :
    HEq (((systemEvaluation S n).map
      ((reductionComparison R S a c d e h A).hom.app M)).val.app U
        (((strictTransportLevel a n).inv.app ((reductionFunctor R c A).obj M)).val.app U
          (((reductionEvaluation R c A n).inv.app M).val.app U
            (systemModelTmul (A (c.π.app (op n))).model M U r x))))
      (((reductionEvaluation S d A n).inv.app ((transport e).obj M)).val.app U
        (systemModelTmul (A (d.π.app (op n))).model ((transport e).obj M) U
          ((a.app (op n)).hom.hom.app U r) x)) := by
  change HEq
    ((((ordinaryScalarSquare _ _ e (a.app (op n)) (h n)
      (A (c.π.app (op n))) (A (d.π.app (op n))))).hom.app M).val.app U
      (systemModelTmul (A (c.π.app (op n))).model M U r x))
    (systemModelTmul (A (d.π.app (op n))).model ((transport e).obj M) U
      ((a.app (op n)).hom.hom.app U r) x)
  exact heq_of_eq (ordinaryScalarSquare_tmul _ _ e (a.app (op n)) (h n)
    (A (c.π.app (op n))) (A (d.π.app (op n))) M U x r)

private theorem reductionPreserves (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J))
    {K L : CochainComplex (Modules c.pt) ℤ} (f : K ⟶ L)
    (hK : K.IsKFlatIndependentCoefficients) (hL : L.IsKFlatIndependentCoefficients)
    (hf : QuasiIso f) :
    QuasiIso (((reductionFunctor B c A).mapHomologicalComplex (.up ℤ)).map f) := by
  apply (strictRingSystem_quasiIso_iff B _).2
  intro n
  exact (A (c.π.app (op n))).model.preserves f hK hL hf

private theorem reductionTransition_normalized
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (M : Modules c.pt) {m n : ℕ} (h : m ≤ n)
    (U : Cᵒᵖ) (r : (B.obj (op n)).obj.obj U) (x : M.val.obj U) :
    (((reductionEvaluation B c A m).hom.app M).val.app U
      ((((reductionFunctor B c A).obj M).transition h).val.app U
        (((reductionEvaluation B c A n).inv.app M).val.app U
          (systemModelTmul (A (c.π.app (op n))).model M U r x)))) =
      systemModelTmul (A (c.π.app (op m))).model M U
        ((B.map (homOfLE h).op).hom.app U r) x :=
  reductionTransition_tmul B c A M h U r x

attribute [local irreducible] reductionFunctor

private theorem existsDerivedPair
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory D]
    (E : A ⥤ D) [E.Additive] (p : CochainComplex A ℤ → Prop)
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (L : CochainComplex A ℤ) (f : L ⟶ K), p L ∧ QuasiIso f)
    (inv : ∀ {K L : CochainComplex A ℤ} (f : K ⟶ L), p K → p L → QuasiIso f →
      QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f)) :
    ∃ (T : DerivedCategory A ⥤ DerivedCategory D)
      (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
      T.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ)) ∧
      Functor.HasPointwiseLeftDerivedFunctor
        (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        (HomologicalComplex.quasiIso A (.up ℤ)) ∧
      ∀ K, p K → IsIso (ε.app K) := by
  classical
  let q := HomotopyCategory.quotient A (.up ℤ)
  let WA := HomotopyCategory.quasiIso A (.up ℤ)
  let WD := HomotopyCategory.quasiIso D (.up ℤ)
  let F := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := D)
  let P : Set (HomotopyCategory A (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex A ℤ, p K ∧ q.obj K = X
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (X' : HomotopyCategory A (.up ℤ)) (s : X' ⟶ X), X' ∈ P ∧ WA s := by
    intro X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, f, hL, hf⟩ := res K
    exact ⟨q.obj L, q.map f, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  have hinv : ∀ (X X' : HomotopyCategory A (.up ℤ)) (s : X ⟶ X'),
      X ∈ P → X' ∈ P → WA s → IsIso (F.map s) := by
    rintro X X' s ⟨K, hK, rfl⟩ ⟨L, hL, rfl⟩ hs
    obtain ⟨f, rfl⟩ := q.map_surjective s
    have hf := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).1 hs
    have hg := inv f hK hL hf
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient D (.up ℤ)).map
        ((E.mapHomologicalComplex (.up ℤ)).map f)))
    exact Localization.inverts DerivedCategory.Qh WD _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hg)
  obtain ⟨hpw, T, ε, huniv, htri, hcomp⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory D) F P hres hinv
  let : F.HasPointwiseLeftDerivedFunctor WA := hpw
  let : T.IsLeftDerivedFunctor ε WA := huniv
  let α := (Functor.associator q DerivedCategory.Qh T).hom ≫ Functor.whiskerLeft q ε
  have hα := pointwise_precomp_full q DerivedCategory.Qh F T ε
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor T ε WA)
  let i := DerivedCategory.quotientCompQhIso A
  let j : q ⋙ F ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso D)
  let β : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight i.inv T ≫ α ≫ j.hom
  have hβ := pointwise_change_iso T i j α hα
  refine ⟨T, β, ⟨hβ.isRightKanExtension⟩, ?_, ?_⟩
  · intro X
    exact (Functor.hasPointwiseLeftDerivedFunctorAt_iff
      (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) DerivedCategory.Q
        (HomologicalComplex.quasiIso A (.up ℤ)) X).2
      ((hβ _).hasPointwiseRightKanExtensionAt)
  · intro K hK
    have := hcomp (q.obj K) ⟨K, hK, rfl⟩
    dsimp [β, α]
    infer_instance

private theorem comparisonFromResolutions
    {A₀ D : Type*} [Category A₀] [Abelian A₀] [HasDerivedCategory A₀] [Category D]
    (p : CochainComplex A₀ ℤ → Prop)
    (res : ∀ K : CochainComplex (A₀) ℤ,
      ∃ (P : CochainComplex (A₀) ℤ) (f : P ⟶ K), p P ∧ QuasiIso f)
    (U V : DerivedCategory (A₀) ⥤ D) (H : CochainComplex (A₀) ℤ ⥤ D)
    (η : DerivedCategory.Q ⋙ U ⟶ H) (θ : DerivedCategory.Q ⋙ V ⟶ H)
    (hη : ∀ P, p P → IsIso (η.app P)) (hθ : ∀ P, p P → IsIso (θ.app P)) :
    ∃ b : U ≅ V, ∀ K, b.hom.app (DerivedCategory.Q.obj K) ≫ θ.app K = η.app K := by
  obtain ⟨b, hb, _⟩ := comparison_from_resolutions p res U V H η θ hη hθ
  refine ⟨b, fun K ↦ ?_⟩
  obtain ⟨P, f, hP, hf⟩ := res K
  let : QuasiIso f := hf
  apply (cancel_epi (U.map (DerivedCategory.Q.map f))).1
  rw [← Category.assoc, b.hom.naturality, Category.assoc]
  change b.hom.app (DerivedCategory.Q.obj P) ≫ (DerivedCategory.Q ⋙ V).map f ≫
    θ.app K = (DerivedCategory.Q ⋙ U).map f ≫ η.app K
  rw [θ.naturality, ← Category.assoc, hb P hP, η.naturality]

private theorem reductionResolution (B : Sheaf J CommRingCat.{w})
    (K : CochainComplex (Modules B) ℤ) :
    ∃ (P : CochainComplex (Modules B) ℤ) (f : P ⟶ K),
      (P.IsKFlatIndependentCoefficients ∧ ∀ i : ℤ, IsFlatOnSite (R := B) (P.X i)) ∧
        QuasiIso f := by
  obtain ⟨P, q, hP, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := B) K
  exact ⟨P, q, ⟨hP, fun i ↦ (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso B (P.X i)).symm (hflat i)⟩, hq⟩

private structure DerivedReductionPackage
    (T : Sort*) (E : T → Sort*) (V : T → Sort*)
    (P : ∀ t, E t → V t → Prop) where
  derived : T
  counit : E derived
  derivedEvaluation : V derived
  conditions : P derived counit derivedEvaluation

private abbrev ReductionDerivedData
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J))
    (E : Modules c.pt ⥤ StrictRingSystem B) [E.Additive]
    (evaluation : ∀ n : ℕ, E ⋙ systemEvaluation B n ≅ (A (c.π.app (op n))).model.E) :=
  DerivedReductionPackage
    (DerivedCategory (Modules c.pt) ⥤ DerivedCategory (StrictRingSystem B))
    (fun derived ↦
      DerivedCategory.Q ⋙ derived ⟶
    E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (fun derived ↦
      ∀ n : ℕ,
    derived ⋙ derivedSystemEvaluation B n ≅ (A (c.π.app (op n))).model.T)
    (fun derived counit derivedEvaluation ↦
      (derived.IsLeftDerivedFunctor counit (HomologicalComplex.quasiIso _ (.up ℤ))) ∧
      (Functor.HasPointwiseLeftDerivedFunctor
    (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (HomologicalComplex.quasiIso _ (.up ℤ))) ∧
      (∀ P : CochainComplex (Modules c.pt) ℤ,
    P.IsKFlatIndependentCoefficients → (∀ i : ℤ, IsFlatOnSite (R := c.pt) (P.X i)) →
      IsIso (counit.app P)) ∧
      (∀ (n : ℕ) (P : CochainComplex (Modules c.pt) ℤ),
    (derivedEvaluation n).hom.app (DerivedCategory.Q.obj P) ≫
        (A (c.π.app (op n))).model.ε.app P =
      (derivedSystemEvaluation B n).map (counit.app P) ≫
        (systemEvaluation B n).mapDerivedCategoryFactors.hom.app
          ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (evaluation n) (.up ℤ)).hom.app P)))

private abbrev ReductionDerivedModel
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) :=
  ReductionDerivedData B c A (reductionFunctor B c A) (reductionEvaluation B c A)

private abbrev reduction (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) (D : ReductionDerivedModel B c A) :
    Reduction B c A where
  ordinary := reductionFunctor B c A
  additive := reductionFunctorAdditive B c A
  evaluation := reductionEvaluation B c A
  derived := D.derived
  counit := D.counit
  derivedEvaluation := D.derivedEvaluation
  conditions := ⟨reductionTransition_normalized B c A, D.conditions.1,
    D.conditions.2.1, D.conditions.2.2.1, D.conditions.2.2.2⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem nonemptyReductionDerivedData (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J))
    (E : Modules c.pt ⥤ StrictRingSystem B) [E.Additive]
    (ev : ∀ n : ℕ, E ⋙ systemEvaluation B n ≅ (A (c.π.app (op n))).model.E)
    (hp : ∀ {K L : CochainComplex (Modules c.pt) ℤ} (f : K ⟶ L),
      K.IsKFlatIndependentCoefficients → L.IsKFlatIndependentCoefficients → QuasiIso f →
        QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f)) :
    Nonempty (ReductionDerivedData B c A E ev) := by
  let p : CochainComplex (Modules c.pt) ℤ → Prop := fun P ↦
    P.IsKFlatIndependentCoefficients ∧ ∀ i : ℤ, IsFlatOnSite (R := c.pt) (P.X i)
  obtain ⟨T, ε, hT, hpw, hcomp⟩ := existsDerivedPair E p (reductionResolution c.pt)
    (fun f hK hL hf ↦ hp f hK.1 hL.1 hf)
  let := hT
  let η (n : ℕ) : DerivedCategory.Q ⋙ (T ⋙ derivedSystemEvaluation B n) ⟶
      (A (c.π.app (op n))).model.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight ε (derivedSystemEvaluation B n) ≫
      Functor.whiskerLeft (E.mapHomologicalComplex (.up ℤ))
        (systemEvaluation B n).mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight (NatIso.mapHomologicalComplex
        (ev n) (.up ℤ)).hom DerivedCategory.Q
  have hn (n : ℕ) : ∃ b : T ⋙ derivedSystemEvaluation B n ≅
      (A (c.π.app (op n))).model.T,
      ∀ P, b.hom.app (DerivedCategory.Q.obj P) ≫
        (A (c.π.app (op n))).model.ε.app P = (η n).app P := by
    apply comparisonFromResolutions p (reductionResolution c.pt) _ _ _
      (η n) (A (c.π.app (op n))).model.ε
    · intro P hP
      let : IsIso (ε.app P) := hcomp P hP
      change IsIso ((derivedSystemEvaluation B n).map (ε.app P) ≫
        (systemEvaluation B n).mapDerivedCategoryFactors.hom.app
          ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (ev n) (.up ℤ)).hom.app P))
      infer_instance
    · intro P hP
      exact (A (c.π.app (op n))).model.computes P hP.1
  choose b hb using hn
  exact ⟨{
    derived := T
    counit := ε
    derivedEvaluation := b
    conditions := ⟨hT, hpw, fun P hP hflat ↦ hcomp P ⟨hP, hflat⟩, hb⟩ }⟩

private theorem nonemptyReductionDerivedModel (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone B)
    (A : SystemScalarAssignment (J := J)) : Nonempty (ReductionDerivedModel B c A) :=
  nonemptyReductionDerivedData B c A (reductionFunctor B c A) (reductionEvaluation B c A)
    (fun f hK hL hf ↦ reductionPreserves B c A f hK hL hf)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem existsDerivedReductionComparison
    (R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (a : R ≅ S)
    (c : Cone R) (d : Cone S) (e : c.pt ≅ d.pt)
    (h : ∀ n, e.hom ≫ d.π.app (op n) = c.π.app (op n) ≫ (a.app (op n)).hom)
    (A : SystemScalarAssignment (J := J))
    (DR : ReductionDerivedModel R c A) (DS : ReductionDerivedModel S d A) :
    ∃ b : DR.derived ⋙ (strictTransportFunctor a).mapDerivedCategory ≅
      (transport e).mapDerivedCategory ⋙ DS.derived,
      ∀ P : CochainComplex (Modules c.pt) ℤ,
      b.hom.app (DerivedCategory.Q.obj P) ≫
          DS.derived.map ((transport e).mapDerivedCategoryFactors.hom.app P) ≫
          DS.counit.app (((transport e).mapHomologicalComplex (.up ℤ)).obj P) =
        (strictTransportFunctor a).mapDerivedCategory.map (DR.counit.app P) ≫
          (strictTransportFunctor a).mapDerivedCategoryFactors.hom.app
            (((reductionFunctor R c A).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (reductionComparison R S a c d e h A) (.up ℤ)).hom.app P) := by
  let P := (scalarTransportEquivalence e).mapHomologicalComplex (.up ℤ)
  let E := (transport e).mapDerivedCategory.asEquivalence
  let G := (strictTransportFunctor a).mapDerivedCategory.asEquivalence
  let F := ((reductionFunctor R c A).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q
  let F' := ((reductionFunctor S d A).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q
  let eL : DerivedCategory.Q ⋙ E.functor ≅ P.functor ⋙ DerivedCategory.Q :=
    (transport e).mapDerivedCategoryFactors
  let eF : F ⋙ G.functor ≅ P.functor ⋙ F' :=
    Functor.isoWhiskerLeft ((reductionFunctor R c A).mapHomologicalComplex (.up ℤ))
      (strictTransportFunctor a).mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight (NatIso.mapHomologicalComplex
        (reductionComparison R S a c d e h A) (.up ℤ)) DerivedCategory.Q
  let : DR.derived.IsRightKanExtension DR.counit :=
    let : DR.derived.IsLeftDerivedFunctor DR.counit
        (HomologicalComplex.quasiIso _ (.up ℤ)) := DR.conditions.1
    Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomologicalComplex.quasiIso _ (.up ℤ))
  let : DS.derived.IsRightKanExtension DS.counit :=
    let : DS.derived.IsLeftDerivedFunctor DS.counit
        (HomologicalComplex.quasiIso _ (.up ℤ)) := DS.conditions.1
    Functor.IsLeftDerivedFunctor.isRightKanExtension _ _
      (HomologicalComplex.quasiIso _ (.up ℤ))
  refine ⟨kanSquareIso P E G DerivedCategory.Q DerivedCategory.Q F F'
    DR.derived DS.derived DR.counit DS.counit eL eF, fun K ↦ ?_⟩
  have hK := NatTrans.congr_app (kanSquareIso_fac P E G DerivedCategory.Q
    DerivedCategory.Q F F' DR.derived DS.derived DR.counit DS.counit eL eF) K
  simpa only [P, E, G, F, F', eL, eF, Functor.asEquivalence_functor,
    Equivalence.mapHomologicalComplex_functor, scalarTransportEquivalence,
    kanSquareCounit, kanSquarePostCounit,
    NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.trans_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
    using hK

private theorem exactUnitSquare
    {D E : Type*} [Category D] [Category E] [Abelian D] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (R : D ⥤ D) (S : E ⥤ E) (T : D ⥤ E)
    [R.Additive] [S.Additive] [T.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (ρ : R ⋙ T ≅ T ⋙ S) (η : R ≅ 𝟭 D) (θ : S ≅ 𝟭 E)
    (h : ∀ X, ρ.hom.app X ≫ θ.hom.app (T.obj X) = T.map (η.hom.app X))
    (M : DerivedCategory D) :
    (Functor.mapDerivedCategorySquareIso ρ).hom.app M ≫
        (Functor.exactDerivedRestrictionUnit S θ).hom.app (T.mapDerivedCategory.obj M) =
      T.mapDerivedCategory.map ((Functor.exactDerivedRestrictionUnit R η).hom.app M) := by
  have hρ : ρ ≪≫ Functor.isoWhiskerLeft T θ = Functor.isoWhiskerRight η T := by
    ext X
    exact h X
  have hd := congrArg (fun i ↦ (Functor.mapDerivedCategoryNatIso i).hom) hρ
  rw [Functor.mapDerivedCategoryNatIso_trans] at hd
  have hl := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft T θ
  have hr := Functor.mapDerivedCategoryNatIso_isoWhiskerRight η T
  have hul := Functor.mapDerivedCategoryCompIso_id_comp T
  have hur := Functor.mapDerivedCategoryCompIso_comp_id T
  have hl' := congrArg (fun t ↦ t ≫ Functor.whiskerLeft T.mapDerivedCategory
    (Functor.mapDerivedCategoryIdIso E).hom) hl
  have hr' := congrArg (fun t ↦ t ≫ Functor.whiskerRight
    (Functor.mapDerivedCategoryIdIso D).hom T.mapDerivedCategory) hr
  simp only [Category.assoc, hur, Category.comp_id] at hl'
  simp only [Category.assoc, hul, Category.comp_id] at hr'
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso R T).hom.app M)).1
  simp only [Functor.mapDerivedCategorySquareIso, Functor.exactDerivedRestrictionUnit,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  have hlM := NatTrans.congr_app hl' M
  have hrM := NatTrans.congr_app hr' M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hlM hrM
  rw [← hlM, ← hrM]
  simpa only [NatTrans.comp_app, Category.assoc] using
    congrArg (fun f ↦ f ≫ NatTrans.app (𝟙 T.mapDerivedCategory) M) (NatTrans.congr_app hd M)

private theorem derivedQuotientUnit
    (R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (a : R ≅ S)
    (A : SystemScalarAssignment (J := J)) (n : ℕ)
    (M : DerivedCategory (systemLevel R n)) :
    (transport (a.app (op n))).mapDerivedCategory.map
        (((systemTensorCoherence A).derivedUnit R n).hom.app M) =
      (derivedScalarSquare _ _ (a.app (op n)) (a.app (op n))
        (a.hom.naturality (homOfLE (Nat.le_refl n)).op).symm
        (A (R.map (homOfLE (Nat.le_refl n)).op))
        (A (S.map (homOfLE (Nat.le_refl n)).op))).hom.app M ≫
        ((systemTensorCoherence A).derivedUnit S n).hom.app
          ((transport (a.app (op n))).mapDerivedCategory.obj M) := by
  let AR := A (R.map (homOfLE (Nat.le_refl n)).op)
  let AS := A (S.map (homOfLE (Nat.le_refl n)).op)
  let ρ := scalarRestrictionSquare (R.map (homOfLE (Nat.le_refl n)).op)
    (S.map (homOfLE (Nat.le_refl n)).op) (a.app (op n)) (a.app (op n))
    (a.hom.naturality (homOfLE (Nat.le_refl n)).op).symm
  let δ := derivedSquare _ _ (a.app (op n)) (a.app (op n)) ρ
  let ι := derivedScalarSquare _ _ (a.app (op n)) (a.app (op n))
    (a.hom.naturality (homOfLE (Nat.le_refl n)).op).symm AR AS
  let uR := (systemTensorCoherence A).derivedUnit R n
  let uS := (systemTensorCoherence A).derivedUnit S n
  have huR := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (AR.adjunction.ofNatIsoRight (systemDerivedRestrictionUnit R n)) Adjunction.id M
  have huS := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (AS.adjunction.ofNatIsoRight (systemDerivedRestrictionUnit S n)) Adjunction.id
    ((transport (a.app (op n))).mapDerivedCategory.obj M)
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at huR huS
  have hR : AR.adjunction.homEquiv _ _ (uR.hom.app M) =
      (systemDerivedRestrictionUnit R n).inv.app M := by
    apply (cancel_mono ((systemDerivedRestrictionUnit R n).hom.app M)).1
    erw [huR, Iso.inv_hom_id_app]
    rfl
  have hS : AS.adjunction.homEquiv _ _
      (uS.hom.app ((transport (a.app (op n))).mapDerivedCategory.obj M)) =
      (systemDerivedRestrictionUnit S n).inv.app
        ((transport (a.app (op n))).mapDerivedCategory.obj M) := by
    apply (cancel_mono ((systemDerivedRestrictionUnit S n).hom.app _)).1
    erw [huS, Iso.inv_hom_id_app]
    rfl
  change (transport (a.app (op n))).mapDerivedCategory.map (uR.hom.app M) =
    ι.hom.app M ≫ uS.hom.app ((transport (a.app (op n))).mapDerivedCategory.obj M)
  apply (cancel_epi (ι.inv.app M)).1
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply (AS.adjunction.homEquiv _ _).injective
  erw [derivedScalarSquare_transpose, hR, hS]
  apply (cancel_mono ((systemDerivedRestrictionUnit S n).hom.app _)).1
  rw [Category.assoc]
  have hd := exactUnitSquare (systemRestriction R (Nat.le_refl n))
    (systemRestriction S (Nat.le_refl n)) (transport (a.app (op n))) ρ
    (systemScalarRestrictionUnit _ (R.map_id (op n)))
    (systemScalarRestrictionUnit _ (S.map_id (op n)))
    (by intro X; ext U x; rfl) M
  rw [← derivedSquare_eq] at hd
  change δ.hom.app M ≫ (systemDerivedRestrictionUnit S n).hom.app _ =
    (transport (a.app (op n))).mapDerivedCategory.map
      ((systemDerivedRestrictionUnit R n).hom.app M) at hd
  erw [hd, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Iso.inv_hom_id_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryQuotientUnit
    (R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (a : R ≅ S)
    (A : SystemScalarAssignment (J := J)) (n : ℕ) (M : systemLevel R n) :
    (transport (a.app (op n))).map
        (((systemTensorCoherence A).ordinaryUnit R n).hom.app M) =
      (ordinaryScalarSquare _ _ (a.app (op n)) (a.app (op n))
          (a.hom.naturality (homOfLE (Nat.le_refl n)).op).symm
          (A (R.map (homOfLE (Nat.le_refl n)).op))
          (A (S.map (homOfLE (Nat.le_refl n)).op))).hom.app M ≫
        ((systemTensorCoherence A).ordinaryUnit S n).hom.app
          ((transport (a.app (op n))).obj M) := by
  apply transportedTensorHomExt (A (R.map (homOfLE (Nat.le_refl n)).op))
    (a.app (op n))
  intro U x
  change (((systemTensorCoherence A).ordinaryUnit R n).hom.app M).val.app U _ = _
  rw [(systemTensorCoherence A).unit_normalized]
  change (1 : (R.obj (op n)).obj.obj U) • x =
    (((systemTensorCoherence A).ordinaryUnit S n).hom.app
      ((transport (a.app (op n))).obj M)).val.app U
      (((ordinaryScalarSquare _ _ (a.app (op n)) (a.app (op n)) _ _ _).hom.app M).val.app U _)
  rw [ordinaryScalarSquare_tmul, (systemTensorCoherence A).unit_normalized]
  simp only [map_one, one_smul]

private def strictDerivedLevel
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S) (n : ℕ) :
    (strictTransportFunctor a).mapDerivedCategory ⋙ derivedSystemEvaluation S n ≅
      derivedSystemEvaluation R n ⋙ (transport (a.app (op n))).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (strictTransportLevel a n)

private theorem exactTransitionSquare
    {A₀ B₀ C₀ C₁ D₀ D₁ : Type*}
    [Category A₀] [Category B₀] [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    [Abelian A₀] [Abelian B₀] [Abelian C₀] [Abelian C₁] [Abelian D₀] [Abelian D₁]
    [HasDerivedCategory A₀] [HasDerivedCategory B₀]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory D₀] [HasDerivedCategory D₁]
    (F : A₀ ⥤ B₀) (V₀ : A₀ ⥤ C₀) (V₁ : A₀ ⥤ C₁)
    (W₀ : B₀ ⥤ D₀) (W₁ : B₀ ⥤ D₁)
    (R₀ : C₀ ⥤ C₁) (S₀ : D₀ ⥤ D₁) (T₀ : C₀ ⥤ D₀) (T₁ : C₁ ⥤ D₁)
    [F.Additive] [V₀.Additive] [V₁.Additive] [W₀.Additive] [W₁.Additive]
    [R₀.Additive] [S₀.Additive] [T₀.Additive] [T₁.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits V₀] [PreservesFiniteColimits V₀]
    [PreservesFiniteLimits V₁] [PreservesFiniteColimits V₁]
    [PreservesFiniteLimits W₀] [PreservesFiniteColimits W₀]
    [PreservesFiniteLimits W₁] [PreservesFiniteColimits W₁]
    [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]
    [PreservesFiniteLimits S₀] [PreservesFiniteColimits S₀]
    [PreservesFiniteLimits T₀] [PreservesFiniteColimits T₀]
    [PreservesFiniteLimits T₁] [PreservesFiniteColimits T₁]
    (τ : V₁ ⟶ V₀ ⋙ R₀) (σ : W₁ ⟶ W₀ ⋙ S₀)
    (q₀ : F ⋙ W₀ ≅ V₀ ⋙ T₀) (q₁ : F ⋙ W₁ ≅ V₁ ⋙ T₁)
    (ρ : R₀ ⋙ T₁ ≅ T₀ ⋙ S₀)
    (h₀ : ∀ X, q₁.hom.app X ≫ T₁.map (τ.app X) ≫ ρ.hom.app (V₀.obj X) =
      σ.app (F.obj X) ≫ S₀.map (q₀.hom.app X))
    (τD : V₁.mapDerivedCategory ⟶ V₀.mapDerivedCategory ⋙ R₀.mapDerivedCategory)
    (σD : W₁.mapDerivedCategory ⟶ W₀.mapDerivedCategory ⋙ S₀.mapDerivedCategory)
    (τrep : ∀ K : CochainComplex A₀ ℤ,
      τD.app (DerivedCategory.Q.obj K) ≫
        R₀.mapDerivedCategory.map (V₀.mapDerivedCategoryFactors.hom.app K) ≫
        R₀.mapDerivedCategoryFactors.hom.app ((V₀.mapHomologicalComplex (.up ℤ)).obj K) =
      V₁.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((τ.mapHomologicalComplex (.up ℤ)).app K))
    (σrep : ∀ K : CochainComplex B₀ ℤ,
      σD.app (DerivedCategory.Q.obj K) ≫
        S₀.mapDerivedCategory.map (W₀.mapDerivedCategoryFactors.hom.app K) ≫
        S₀.mapDerivedCategoryFactors.hom.app ((W₀.mapHomologicalComplex (.up ℤ)).obj K) =
      W₁.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((σ.mapHomologicalComplex (.up ℤ)).app K))
    (M : DerivedCategory A₀) :
    (Functor.mapDerivedCategorySquareIso q₁).hom.app M ≫ T₁.mapDerivedCategory.map (τD.app M) ≫
      (Functor.mapDerivedCategorySquareIso ρ).hom.app (V₀.mapDerivedCategory.obj M) =
    σD.app (F.mapDerivedCategory.obj M) ≫
      S₀.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso q₀).hom.app M) := by
  let δ := Functor.mapDerivedCategorySquareIso ρ
  let α : F.mapDerivedCategory ⋙ W₁.mapDerivedCategory ⟶
      V₀.mapDerivedCategory ⋙ T₀.mapDerivedCategory ⋙
        (S₀).mapDerivedCategory :=
    (Functor.mapDerivedCategorySquareIso q₁).hom ≫
      Functor.whiskerRight (τD) T₁.mapDerivedCategory ≫
      Functor.whiskerLeft V₀.mapDerivedCategory δ.hom
  let β : F.mapDerivedCategory ⋙ W₁.mapDerivedCategory ⟶
      V₀.mapDerivedCategory ⋙ T₀.mapDerivedCategory ⋙
        (S₀).mapDerivedCategory :=
    Functor.whiskerLeft F.mapDerivedCategory (σD) ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso q₀).hom (S₀).mapDerivedCategory
  have he : α = β := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (A₀) (.up ℤ))
    intro K
    let Km := (V₀.mapHomologicalComplex (.up ℤ)).obj K
    have hc :
        ((NatIso.mapHomologicalComplex (q₁) (.up ℤ)).hom.app K) ≫
            (T₁.mapHomologicalComplex (.up ℤ)).map
              (((τ).mapHomologicalComplex (.up ℤ)).app K) ≫
            (NatIso.mapHomologicalComplex ρ (.up ℤ)).hom.app Km =
          (((σ).mapHomologicalComplex (.up ℤ)).app
            ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
            ((S₀).mapHomologicalComplex (.up ℤ)).map
              ((NatIso.mapHomologicalComplex (q₀) (.up ℤ)).hom.app K) := by
      apply HomologicalComplex.hom_ext
      intro i
      exact h₀ (K.X i)
    apply (cancel_mono ((S₀).mapDerivedCategory.map
      (T₀.mapDerivedCategory.map (V₀.mapDerivedCategoryFactors.hom.app K) ≫
        T₀.mapDerivedCategoryFactors.hom.app Km) ≫
      (S₀).mapDerivedCategoryFactors.hom.app
        ((T₀.mapHomologicalComplex (.up ℤ)).obj Km))).1
    dsimp only [α, β, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    simp only [Functor.map_comp, Category.assoc]
    erw [← δ.hom.naturality_assoc]
    erw [Functor.exactSquare_fac ρ Km]
    erw [← T₁.mapDerivedCategory.map_comp_assoc, ← T₁.mapDerivedCategory.map_comp_assoc]
    have ht := (Category.assoc (τD.app (DerivedCategory.Q.obj K))
      (R₀.mapDerivedCategory.map (V₀.mapDerivedCategoryFactors.hom.app K))
      (R₀.mapDerivedCategoryFactors.hom.app Km)).trans (τrep K)
    erw [ht]
    erw [T₁.mapDerivedCategory.map_comp]
    erw [Category.assoc
      (T₁.mapDerivedCategory.map (V₁.mapDerivedCategoryFactors.hom.app K))
      (T₁.mapDerivedCategory.map
        (DerivedCategory.Q.map ((τ.mapHomologicalComplex (.up ℤ)).app K)))]
    have hn := T₁.mapDerivedCategoryFactors.hom.naturality
      ((τ.mapHomologicalComplex (.up ℤ)).app K)
    dsimp only [Functor.comp_map] at hn
    erw [reassoc_of% hn]
    erw [reassoc_of% (Functor.exactSquare_fac q₁ K)]
    erw [← DerivedCategory.Q.map_comp]
    have hq₀ := (Category.assoc
      ((Functor.mapDerivedCategorySquareIso q₀).hom.app (DerivedCategory.Q.obj K))
      (T₀.mapDerivedCategory.map (V₀.mapDerivedCategoryFactors.hom.app K))
      (T₀.mapDerivedCategoryFactors.hom.app Km)).trans
        (Functor.exactSquare_fac q₀ K)
    erw [← S₀.mapDerivedCategory.map_comp_assoc, ← S₀.mapDerivedCategory.map_comp_assoc, hq₀]
    erw [S₀.mapDerivedCategory.map_comp, S₀.mapDerivedCategory.map_comp]
    erw [Category.assoc
      (S₀.mapDerivedCategory.map (W₀.mapDerivedCategory.map
        (F.mapDerivedCategoryFactors.hom.app K)))]
    erw [Category.assoc (S₀.mapDerivedCategory.map
      (W₀.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K)))]
    have hn₀ := S₀.mapDerivedCategoryFactors.hom.naturality
      ((NatIso.mapHomologicalComplex q₀ (.up ℤ)).hom.app K)
    dsimp only [Functor.comp_map] at hn₀
    erw [hn₀]
    have hnσ := σD.naturality (F.mapDerivedCategoryFactors.hom.app K)
    dsimp only [Functor.comp_map] at hnσ
    erw [← reassoc_of% hnσ]
    erw [reassoc_of% (σrep ((F.mapHomologicalComplex (.up ℤ)).obj K))]
    erw [Category.assoc (W₁.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K)),
      Category.assoc (W₁.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K)),
      ← DerivedCategory.Q.map_comp, hc]
    erw [Category.assoc (W₁.mapDerivedCategoryFactors.hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K)), ← DerivedCategory.Q.map_comp]
    rfl
  exact NatTrans.congr_app he M

attribute [local semireducible] strictTransportFunctor in
private theorem strictDerivedTransitionSquare
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S)
    {m n : ℕ} (h : m ≤ n) (M : DerivedCategory (StrictRingSystem R)) :
    (strictDerivedLevel a n).hom.app M ≫
        (transport (a.app (op n))).mapDerivedCategory.map
          ((systemDerivedTransition R h).app M) ≫
        (derivedSquare _ _ (a.app (op n)) (a.app (op m))
          (scalarRestrictionSquare _ _ _ _ (a.hom.naturality (homOfLE h).op).symm)).hom.app
            ((derivedSystemEvaluation R m).obj M) =
      (systemDerivedTransition S h).app ((strictTransportFunctor a).mapDerivedCategory.obj M) ≫
        (systemRestriction S h).mapDerivedCategory.map ((strictDerivedLevel a m).hom.app M) := by
  rw [derivedSquare_eq]
  apply exactTransitionSquare (strictTransportFunctor a)
    (systemEvaluation R m) (systemEvaluation R n)
    (systemEvaluation S m) (systemEvaluation S n)
    (systemRestriction R h) (systemRestriction S h)
    (transport (a.app (op m))) (transport (a.app (op n)))
    (strictSystemTransition R h) (strictSystemTransition S h)
    (strictTransportLevel a m) (strictTransportLevel a n)
    (scalarRestrictionSquare _ _ _ _ (a.hom.naturality (homOfLE h).op).symm)
    (by intro X; ext U x; rfl)
    (systemDerivedTransition R h) (systemDerivedTransition S h)
    (systemDerivedTransition_rep R h) (systemDerivedTransition_rep S h) M

private theorem adjointTransition_comp (A : SystemScalarAssignment (J := J))
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {l m n : ℕ} (h : l ≤ m) (k : m ≤ n)
    (M : DerivedCategory (StrictRingSystem B)) :
    ((systemTensorCoherence A).derivedAssoc B h k).inv.app
          ((derivedSystemEvaluation B n).obj M) ≫
        (systemDerivedTensor A B h).map (adjointTransition A B k M) ≫
        adjointTransition A B h M = adjointTransition A B (h.trans k) M := by
  apply ((systemDerivedTensorAdj A B (h.trans k)).homEquiv _ _).injective
  dsimp only [adjointTransition]
  rw [Equiv.apply_symm_apply]
  change ((A (B.map (homOfLE (h.trans k)).op)).adjunction.homEquiv _ _)
    (((( (A (B.map (homOfLE k).op)).adjunction.comp
        (A (B.map (homOfLE h).op)).adjunction).ofNatIsoRight
      (systemDerivedRestrictionComposition B h k)).leftAdjointUniq
        (A (B.map (homOfLE (h.trans k)).op)).adjunction).inv.app _ ≫ _ ≫ _) = _
  rw [adjunctionComposition_transpose]
  exact systemDerivedTransition_comp B h k M

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem adjointTransition_transport
    (R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (a : R ≅ S)
    (A : SystemScalarAssignment (J := J))
    (M : DerivedCategory (StrictRingSystem R)) {m n : ℕ} (h : m ≤ n) :
    (derivedScalarSquare _ _ (a.app (op n)) (a.app (op m))
      (a.hom.naturality (homOfLE h).op).symm
      (A (R.map (homOfLE h).op)) (A (S.map (homOfLE h).op))).inv.app
        ((derivedSystemEvaluation R n).obj M) ≫
        (transport (a.app (op m))).mapDerivedCategory.map (adjointTransition A R h M) ≫
        (strictDerivedLevel a m).inv.app M =
      (systemDerivedTensor A S h).map ((strictDerivedLevel a n).inv.app M) ≫
        adjointTransition A S h ((strictTransportFunctor a).mapDerivedCategory.obj M) := by
  let AR := A (R.map (homOfLE h).op)
  let AS := A (S.map (homOfLE h).op)
  let δ := derivedSquare _ _ (a.app (op n)) (a.app (op m))
    (scalarRestrictionSquare _ _ _ _ (a.hom.naturality (homOfLE h).op).symm)
  apply (AS.adjunction.homEquiv _ _).injective
  rw [← Category.assoc, AS.adjunction.homEquiv_naturality_right]
  rw [derivedScalarSquare_inv]
  erw [adjunctionMate_transpose]
  dsimp only [adjointTransition]
  rw [Equiv.apply_symm_apply, AS.adjunction.homEquiv_naturality_left]
  erw [Equiv.apply_symm_apply]
  apply (cancel_epi ((strictDerivedLevel a n).hom.app M)).1
  apply (cancel_mono ((systemRestriction S h).mapDerivedCategory.map
    ((strictDerivedLevel a m).hom.app M))).1
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Iso.hom_inv_id_app_assoc]
  erw [(systemRestriction S h).mapDerivedCategory.map_id, Category.comp_id]
  exact strictDerivedTransitionSquare a h M

private theorem adjointTransition_isIso_iff
    (R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (a : R ≅ S)
    (A : SystemScalarAssignment (J := J))
    (M : DerivedCategory (StrictRingSystem R)) {m n : ℕ} (h : m ≤ n) :
    IsIso (adjointTransition A R h M) ↔
      IsIso (adjointTransition A S h ((strictTransportFunctor a).mapDerivedCategory.obj M)) := by
  let T := transport (a.app (op m))
  let : T.IsEquivalence := (scalarTransportEquivalence (a.app (op m))).isEquivalence_functor
  have he := congrArg IsIso (adjointTransition_transport R S a A M h)
  rw [isIso_comp_left_iff, isIso_comp_right_iff, isIso_comp_left_iff,
    isIso_iff_of_reflects_iso] at he
  exact iff_of_eq he

private def strictDerivedEquivalence
    {R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : R ≅ S) :
    DerivedCategory (StrictRingSystem R) ≌ DerivedCategory (StrictRingSystem S) :=
  (strictTransportFunctor a).mapDerivedCategory.asEquivalence

private theorem nonemptyCoherentTransport
    (R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (a : R ≅ S)
    (c : Cone R) (d : Cone S) (e : c.pt ≅ d.pt)
    (h : ∀ n, e.hom ≫ d.π.app (op n) = c.π.app (op n) ≫ (a.app (op n)).hom)
    (A : SystemScalarAssignment (J := J)) : Nonempty (CoherentTransport R S a c d e A) := by
  obtain ⟨DR⟩ := nonemptyReductionDerivedModel R c A
  obtain ⟨DS⟩ := nonemptyReductionDerivedModel S d A
  obtain ⟨b, hb⟩ := existsDerivedReductionComparison R S a c d e h A DR DS
  refine ⟨{
  equivalence := strictTransportEquivalence a
  additive := strictTransportAdditive a
  limits := strictTransportLimits a
  colimits := strictTransportColimits a
  derivedEquivalence := strictDerivedEquivalence a
  localization := (strictTransportFunctor a).mapDerivedCategoryFactors
  level := strictTransportLevel a
  derivedLevel := strictDerivedLevel a
  reductionR := reduction R c A DR
  reductionS := reduction S d A DS
  reduction := reductionComparison R S a c d e h A
  derivedReduction := b
  projection := fun n ↦ scalarSquare _ _ e (a.app (op n)) (h n)
    (A (c.π.app (op n))) (A (d.π.app (op n)))
  quotient := fun k ↦ scalarSquare _ _ _ _ (a.hom.naturality (homOfLE k).op).symm
    (A (R.map (homOfLE k).op)) (A (S.map (homOfLE k).op))
  conditions := ?_ }⟩
  refine ⟨?_, ?_, ?_, rfl, HEq.rfl, ?_, ?_, ?_, hb,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact strictTransport_level a
  · exact strictTransport_transition a
  · exact strictTransport_map a
  · exact strictTransport_level_sections a
  · intro n P
    exact Functor.exactSquare_fac (strictTransportLevel a n) P
  · intro M n U r x
    exact reductionComparison_tmul R S a c d e h A M n U r x
  · exact ordinaryQuotientUnit R S a A
  · intro l m n k j M
    exact scalarOrdinaryAssoc _ _ _ (by rw [← R.map_comp]; rfl)
      _ _ _ (by rw [← S.map_comp]; rfl)
      (a.app (op n)) (a.app (op m)) (a.app (op l))
      (a.hom.naturality (homOfLE j).op).symm (a.hom.naturality (homOfLE k).op).symm
      (a.hom.naturality (homOfLE (k.trans j)).op).symm
      (A _) (A _) (A _) (A _) (A _) (A _) M
  · exact derivedQuotientUnit R S a A
  · intro l m n k j M
    exact scalarDerivedAssoc _ _ _ (by rw [← R.map_comp]; rfl)
      _ _ _ (by rw [← S.map_comp]; rfl)
      (a.app (op n)) (a.app (op m)) (a.app (op l))
      (a.hom.naturality (homOfLE j).op).symm (a.hom.naturality (homOfLE k).op).symm
      (a.hom.naturality (homOfLE (k.trans j)).op).symm
      (A _) (A _) (A _) (A _) (A _) (A _) M
  · exact systemDerivedTransition_tensorUnit R A
  · exact systemDerivedTransition_tensorUnit S A
  · exact fun k j M ↦ adjointTransition_comp A R k j M
  · exact fun k j M ↦ adjointTransition_comp A S k j M
  · exact adjointTransition_transport R S a A
  · intro M
    exact forall_congr' (fun m ↦ forall_congr' (fun n ↦ forall_congr'
      (fun k ↦ adjointTransition_isIso_iff R S a A M k)))

/-- Compatible coefficient-ring isomorphisms transport the whole strict reduction
system, its ordinary unbounded derived category, normalized scalar adjunctions and
transition-adjoint isomorphism condition.

Source: def-pur-section-invariant, finite-clopen expansion, retained steps 2--3 and 5;
Stacks 03D7, 03EK, 015F, 06YY and 07A6
(blueprint: lem-pur-ring-iso-quotient-system-transport).

Proof:
1. Use the two limit universal properties to construct the coefficient isomorphism
   and its projection equations. Restrict each level along its inverse. The commuting
   ring square makes each old transition semilinear for the new coefficients; its
   underlying section map is unchanged. Restricting back gives a strict inverse.
2. This additive equivalence preserves finite limits and colimits. Localize the
   termwise equivalence, using mapDerivedCategoryFactors as the localization map.
3. For every coefficient square, take the inverse of the inverse mate of its
   restriction comparison. The normalized scalar adjunction units and linearity
   identify its action on r tensor x with alpha(r) tensor x. The mate transpose
   formula identifies the complete Hom correspondences. Their given cochain
   transposes and exact localization squares give the derived representative formula.
4. Construct ordinary reduction levelwise using the recorded scalar models. Define
   its transitions by transposing the canonical scalar compositor. Unit tensors
   generate, so the tensor formulas prove its identities, composition, naturality
   and the strict transport comparison.
5. Flat-term K-flat resolutions exist. Reduction inverts quasi-isomorphisms between
   these inputs levelwise, and exact system evaluation detects quasi-isomorphisms.
   Apply the resolving-class criterion on homotopy categories and transfer its
   pointwise universal pair to cochains. Compare its evaluations with the given
   scalar derived models on resolving inputs. Naturality along a resolution extends
   every representative equation to arbitrary complexes. Exact equivalences preserve
   right Kan extensions. Their universal comparison gives the whole-system derived
   transport map on every complex. All derived data are determined by universal pairs.
6. Uniqueness of normalized adjunction comparisons identifies both ordinary and
   derived unit and compositor squares. The restriction compositors commute before
   localization because their section maps are identities; exact-square composition
   gives the derived square. Thus no iterated tensor resolution is needed here.
7. Exact localization carries the unchanged strict transition square to its derived
   square. Transpose under the normalized scalar adjunctions. The recorded derived
   transition unit and composition laws give the adjoint unit and three-index law.
   The transport square conjugates adjoint transitions by isomorphisms and an
   equivalence, proving preservation and reflection of invertibility. No inverse
   limit of a module system is used.
-/
theorem ringIsoQuotientSystemTransport
    (R S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (a : R ≅ S)
    (c : Cone R) (hc : IsLimit c) (d : Cone S) (hd : IsLimit d)
    (A : SystemScalarAssignment (J := J)) :
    ∃ e : c.pt ≅ d.pt,
      (∀ n : ℕ, e.hom ≫ d.π.app (op n) = c.π.app (op n) ≫ (a.app (op n)).hom) ∧
        Nonempty (CoherentTransport R S a c d e A) := by
  let e := hc.conePointsIsoOfNatIso hd a
  have h (n : ℕ) : e.hom ≫ d.π.app (op n) =
      c.π.app (op n) ≫ (a.app (op n)).hom :=
    hc.conePointsIsoOfNatIso_hom_comp hd a (op n)
  exact ⟨e, h, nonemptyCoherentTransport R S a c d e h A⟩

end SheafOfModules.QuotientIsoTransport
