/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData
import WeilConjectures.AlgebraicGeometry.IntegralTensorPullback.IntegralTensorPullback
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTensorProduct

import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelRealizationSupplement
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift

/-! # Components of the integral direct-image tower argument -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Ordinary integral pullback and tensor preserve the constant-model constructible category.
Source: blueprint latest direct-image.proof.md paragraph (3), first three sentences;
det-lem-int-tensor-pullback and det-lem-int-tensor-product.
Proof: identify spIntegralCondensed with the continuous condensed integer coefficient
presentation of DerivedNakayama.integerRing, retaining multiplication and scalar action.
Transport the existing preserves_and_completed theorem through this coefficient
identification and through leftDerivedUpperStarIsoMapDerivedCategory. Its first clause
is precisely ordinary derived pullback preservation, with no completion. Transport the
first clause of integralTensorProduct through the same coefficient identification and
the existing relative derived tensor presentation. These equivalences preserve cohomology
and finite scalar local models, so the constant-model constructibility predicates agree.
The characteristic hypotheses give p=ringChar k>0 and p≠l. No smoothness is needed.
Zero objects, empty schemes and the tensor unit have the same constructions.
(blueprint: lem-sp-integral-tower-pull-tensor-constructible). -/
theorem integral_pull_tensor_constructible
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    (∀ K : Constructible l E Y,
      constantModelBoundedConstructible (spIntegralCondensed l E) X
        ((pull l E f).obj K.obj)) ∧
    (∀ (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))] (M N : Integral l E T),
      constantModelBoundedConstructible (spIntegralCondensed l E) T M →
      constantModelBoundedConstructible (spIntegralCondensed l E) T N →
      constantModelBoundedConstructible (spIntegralCondensed l E) T
        (((tensor l E T).obj M).obj N)) := by
  have hp : 0 < ringChar k := (Fact.out : (ringChar k).Prime).pos
  have hpl : ringChar k ≠ l := Fact.out
  let assertion (R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) : Prop :=
    ∀ [IsCommMonObj R.X],
      (∀ K : ConstantModelBoundedConstructible R.X Y,
        constantModelBoundedConstructible R.X X
          ((CondensedRing.moduleObjectDerivedPullback R.X f).obj K.obj)) ∧
      (∀ (T : Scheme.{u}) [T.Over (Spec (.of k))]
        [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
        [IsSeparated (T ↘ Spec (.of k))]
        (M N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj R.X T))),
        constantModelBoundedConstructible R.X T M →
        constantModelBoundedConstructible R.X T N →
        constantModelBoundedConstructible R.X T
          (((CondensedRing.derivedTensor R.X T).obj M).obj N))
  have h : assertion (sfbCondensedIntegers l E) := by
    rw [← IntegralConstantModel.pointEquality l E]
    intro
    constructor
    · intro K
      have h := (IntegralTensorPullback.preserves_and_completed l E k (ringChar k)
        hp hpl f K.obj K.property).1
      have := (constantModelConstructibleFiniteTor_wellDefined
        (DerivedNakayama.integerRing l E) X).2.1
      exact ObjectProperty.prop_of_iso _
        ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
          (DerivedNakayama.integerRing l E) f).app K.obj).symm h
    · intro T _ _ _ _ M N hM hN
      exact (integralTensorProduct.{u, u} l E k (ringChar k) hp hpl).1 T M N hM hN
  exact h

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
