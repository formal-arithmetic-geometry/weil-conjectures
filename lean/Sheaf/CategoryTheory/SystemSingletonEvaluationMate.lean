/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F8
-/
module

public import Sheaf.CategoryTheory.SystemEvaluationNormalizationData
import Sheaf.CategoryTheory.DerivedCategory.ExtensionEvaluationComparison

/-! # The singleton comparison as an evaluation mate

Source: Stacks Project, Tags 03D2, 0D6E and 07A6; Zheng, Construction 4.1.
(blueprint: lem-pur-system-singleton-evaluation-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso
  Adjunction.mapDerivedCategoryRightDerivedAdjunction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem cachedRingCompose {T : Type*} [Category T]
    [EssentiallySmall.{w} T] (τ : GrothendieckTopology T) :
    τ.HasSheafCompose (CategoryTheory.forget RingCat.{w}) := inferInstance
private theorem cachedAddCompose {T : Type*} [Category T]
    [EssentiallySmall.{w} T] (τ : GrothendieckTopology T) :
    τ.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w}) := inferInstance
private theorem cachedCommCompose {T : Type*} [Category T]
    [EssentiallySmall.{w} T] (τ : GrothendieckTopology T) :
    τ.HasSheafCompose (CategoryTheory.forget CommRingCat.{w}) := inferInstance
attribute [local instance 20000] cachedRingCompose cachedAddCompose cachedCommCompose
attribute [local instance 20000] comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [EssentiallySmall.{w} D]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  {BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w}}
  {uTop : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))}
  {I : ∀ n : ℕ, AlgebraicInverseImage uTop.inverse (BY.obj (op n)) (BX.obj (op n))}
  (SY : SystemScalarAssignment (J := J)) (TY : SystemTensorCoherence SY)
  (SX : SystemScalarAssignment (J := K)) (TX : SystemTensorCoherence SX)
  (F : SystemGeometricInverseImageData BY BX uTop I)

variable (H : StrictRingSystem BX ⥤ StrictRingSystem BY) [H.Additive]
  [Abelian.HasKInjectiveResolutions (StrictRingSystem BX)]
  (adj : F.functor ⊣ H)
  (Hn : ∀ n : ℕ, systemLevel BX n ⥤ systemLevel BY n)
  [∀ n : ℕ, (Hn n).Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (systemLevel BX n)]
  (adjn : ∀ n : ℕ, F.levelFunctor n ⊣ Hn n)

/-- The specified singleton conjugate is the right mate of exact evaluation.

Source: Zheng, Construction 4.1 and the comparison before Lemma 4.10; Stacks 07A6
(blueprint: lem-pur-system-singleton-evaluation-mate).

Proof: Take the right mate of the inverse-image/evaluation square under the normalized
singleton adjunctions. On a flat-term K-flat representative its inverse is the ordinary
singleton geometric comparison: transpose its ordinary multiplication identity using the
singleton unit, and then use the representative formula for the normalized derived
adjunction. The representative clause in SystemSingletonGeometricComparisons identifies
this with the specified comparison on every resolving complex. Every derived object is
isomorphic to such a representative, so naturality identifies the two singleton maps
on every object. Taking their conjugates under the two composite geometric/singleton
adjunctions gives the claimed equality of right mates, by horizontal mate pasting. -/
theorem systemSingletonEvaluationMate
    (hF : SystemSingletonGeometricComparisons SY TY SX TX F) (n : ℕ) :
    (systemNormalizationEvaluation SY TY SX TX F H adj Hn adjn hF n).hom =
      CategoryTheory.SystemEvaluationNormalization.derivedMate adj (adjn n) (F.evaluation n) := by
  sorry

end SheafOfModules
