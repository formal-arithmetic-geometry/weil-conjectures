/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.RationalTensorComparisonSystem
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients

/-! # Tensor comparisons through rationalization and common finite fields

Source: Weil blueprint, main-20261015, order 1826, final coefficient paragraph,
and order 1868; the conditional descent argument of the DAG
(blueprint: def-sf-common-tensor-comparison-representatives).

All raw localizations and common-stage quotients below are the existing constructions.
The auxiliary records only organize the hypotheses and the normalized conclusions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u c h

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace WeilConjectures.TensorComparisonDescent

attribute [local semireducible] FieldOf

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

variable {l Ω}
  (C : Index l Ω → Type c) [∀ E, Category.{h} (C E)]
  [∀ E, Preadditive (C E)] [∀ E, Linear
      (Integers l Ω E) (C E)]
  [∀ E, MonoidalCategory (C E)] [∀ E, SymmetricCategory (C E)]
  [∀ E, MonoidalPreadditive (C E)] [∀ E, MonoidalLinear (Integers l Ω E) (C E)]

variable (l Ω) in
/-- The actual inclusion of a finite coefficient field into the fixed closure.
Source: blueprint orders 1826, 1868
(blueprint: def-sf-common-tensor-comparison-representatives). -/
def omegaMap (E : Index l Ω) :
    CommRingCat.of (FieldOf l Ω E) ⟶ CommRingCat.of Ω :=
  CommRingCat.ofHom (show FieldOf l Ω E →+* Ω from E.val.subtype)

variable {C} {A : IntegralData C} [RationalStructures C] (R : RationalData C A)

/-- The actual finite-dimensional target functor, restricted by the proved range clause.
Source: blueprint order 1868 (blueprint: def-sf-common-tensor-comparison-representatives). -/
def fdFunctor (E : Index l Ω) : Rat C E ⥤
    (DerivedCategory.pointFiniteDimensional (FieldOf l Ω E)).FullSubcategory :=
  (DerivedCategory.pointFiniteDimensional (FieldOf l Ω E)).lift (R.F E) (R.finite E)

/-- The common-stage image object, retaining its original coefficient field.
Source: blueprint order 1868 (blueprint: def-sf-common-tensor-comparison-representatives). -/
def image (P : R.S.PairCategory) : DerivedCategory.PointFdQbar l Ω :=
  ⟨P.stage, (fdFunctor R P.stage).obj P.obj⟩

/-- Canonical target transport from a larger stage to the fixed pair object, using
precisely the recorded termwise scalar tower. Source: blueprint order 1868
(blueprint: def-sf-common-tensor-comparison-representatives). -/
def imageStage (P : R.S.PairCategory) (L : Index l Ω) (a : P.stage ≤ L) :
    (DerivedCategory.pointFdQbarStage l Ω L).obj
      ((DerivedCategory.pointFdScalarExtension (fieldMap l Ω a).hom).obj
        ((fdFunctor R P.stage).obj P.obj)) ≅ image R P :=
  (DerivedCategory.pointFdQbarStageComp l Ω a).app ((fdFunctor R P.stage).obj P.obj)

/-- The tensor object at a specified common stage. Source: blueprint order 1826
(blueprint: def-sf-common-tensor-comparison-representatives). -/
def tensorAt (P Q : R.S.PairCategory) (K : Index l Ω)
    (a : P.stage ≤ K) (b : Q.stage ≤ K) : Rat C K := P.toStage a ⊗ Q.toStage b

/-- The required source transport d, with both tower comparisons retained.
Source: corrected DAG statement, proof step 7, blueprint order 1826
(blueprint: def-sf-common-tensor-comparison-representatives). -/
def tensorMove (P Q : R.S.PairCategory) (K L : Index l Ω)
    (a : P.stage ≤ K) (b : Q.stage ≤ K) (s : K ≤ L) :
    (R.S.T s).obj (tensorAt R P Q K a b) ≅
      tensorAt R P Q L (a.trans s) (b.trans s) :=
  ((R.transitionTensor s).μIso (P.toStage a) (Q.toStage b)).symm ≪≫
    tensorIso ((R.S.assoc a s).app P.obj) ((R.S.assoc b s).app Q.obj)

/-- The rational tensor comparison at one field, followed by the two scalar comparisons.
Source: corrected DAG statement, proof step 8, blueprint order 1826
(blueprint: def-sf-common-tensor-comparison-representatives). -/
def gamma (P Q : R.S.PairCategory) (L : Index l Ω)
    (a : P.stage ≤ L) (b : Q.stage ≤ L) :
    (R.F L).obj (tensorAt R P Q L a b) ≅
      (DerivedCategory.fieldDerivedScalarExtension (fieldMap l Ω a).hom).obj
          ((R.F P.stage).obj P.obj) ⊗
        (DerivedCategory.fieldDerivedScalarExtension (fieldMap l Ω b).hom).obj
          ((R.F Q.stage).obj Q.obj) :=
  ((R.tensor L).μIso (P.toStage a) (Q.toStage b)).symm ≪≫
    tensorIso ((R.phi a).app P.obj) ((R.phi b).app Q.obj)

/-- The tensor of the two extended target objects at the stated field.
Source: DAG proof steps 7--8, order 1826
(blueprint: def-sf-common-tensor-comparison-representatives). -/
def targetAt (P Q : R.S.PairCategory) (L : Index l Ω)
    (a : P.stage ≤ L) (b : Q.stage ≤ L) : D (FieldOf l Ω L) :=
  (DerivedCategory.fieldDerivedScalarExtension (fieldMap l Ω a).hom).obj
      ((R.F P.stage).obj P.obj) ⊗
    (DerivedCategory.fieldDerivedScalarExtension (fieldMap l Ω b).hom).obj
      ((R.F Q.stage).obj Q.obj)

/-- The stagewise target tensor arrow e. Source: DAG proof steps 7--8, order 1826
(blueprint: def-sf-common-tensor-comparison-representatives). -/
def targetMove (P Q : R.S.PairCategory) (K L : Index l Ω)
    (a : P.stage ≤ K) (b : Q.stage ≤ K) (s : K ≤ L) :
    (DerivedCategory.fieldDerivedScalarExtension (fieldMap l Ω s).hom).obj
      (targetAt R P Q K a b) ⟶ targetAt R P Q L (a.trans s) (b.trans s) :=
  (R.kappa s).inv.app _ ≫
    (scalarTensor (fieldMap l Ω s) _ _
      (R.extendedPerfect a P.obj) (R.extendedPerfect b Q.obj)).hom ≫
    ((R.kappa s).hom.app _ ⊗ₘ (R.kappa s).hom.app _) ≫
    ((DerivedCategory.fieldScalarTower (fieldMap l Ω a).hom (fieldMap l Ω s).hom).hom.app
        ((R.F P.stage).obj P.obj) ⊗ₘ
      (DerivedCategory.fieldScalarTower (fieldMap l Ω b).hom (fieldMap l Ω s).hom).hom.app
        ((R.F Q.stage).obj Q.obj))


end WeilConjectures.TensorComparisonDescent
