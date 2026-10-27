/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Sheaf.Paper.RestrictionOfScalarsExact
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.Paper.IntegralDerivedReduction
public import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Sheaf.Algebra.Homology.DerivedTensor
public import Sheaf.Paper.IntegralOperationsWellDefined
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses

/-! # Integral derived operations

Source: Bhatt--Scholze, Definition 3.4.10 and Lemmas 3.4.11, 3.4.12(4), 6.5.9(4);
Stacks Project, Tag 099N(5) (blueprint: def-pur-integral-derived-operations).

The coefficient completion, positive finite reductions, K-flat representatives,
canonical transition maps and Roos complexes are those of the dependency modules.
The first two functors are their normalized descents, chosen together with their
representative comparisons, which determine them up to unique compatible isomorphism.
Internal Hom is the ambient derived internal Hom over the completed coefficient sheaf.
No derived-completeness or constructibility hypothesis is imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section PullbackDescent

attribute [local instance 3000] integralTowerHasDerivedCategory

/-- A completed pullback descent, its representative comparison, and its universal property.
The record keeps the existing choices together so consumers need not unfold nested existentials.
Source: Bhatt--Scholze, Lemma 6.5.9(4); Stacks Project, Tag 099N(5)
(blueprint: def-trf-integral-pullback-descent-model). -/
structure IntegralPullbackDescent {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y) where
  functor : DerivedCategory (integralTowerModules l E Y) ⥤
    DerivedCategory (integralTowerModules l E X)
  comparison : integralOperationsGoodLocalization l E Y ⋙ functor ≅
    integralOperationsPullbackOnGood l E f
  universal : ∀ (G : DerivedCategory (integralTowerModules l E Y) ⥤
      DerivedCategory (integralTowerModules l E X))
    (e : integralOperationsGoodLocalization l E Y ⋙ G ≅
      integralOperationsPullbackOnGood l E f),
    ∃! i : functor ≅ G,
      Functor.isoWhiskerLeft (integralOperationsGoodLocalization l E Y) i ≪≫ e = comparison

/-- The existing normalized pullback descent, packaged without making a new choice.
Its universal property determines the data up to unique compatible isomorphism.
Source: Bhatt--Scholze, Lemma 6.5.9(4); Stacks Project, Tag 099N(5)
(blueprint: def-trf-integral-pullback-descent-model). -/
noncomputable def integralPullbackDescent {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) : IntegralPullbackDescent l E f where
  functor := (integralOperationsWellDefined l E f X).2.2.choose
  comparison := (integralOperationsWellDefined l E f X).2.2.choose_spec.choose
  universal :=
    (integralOperationsWellDefined l E f X).2.2.choose_spec.choose_spec
      |>.choose_spec.choose_spec.1

end PullbackDescent

/-- Completed integral derived pullback: the normalized descent of
P ↦ Cone(1-s)[-1] on the strict tower Res_n f*(P_n), with n denoting exponent n+1.
Source: Bhatt--Scholze, Lemma 6.5.9(4); Stacks Project, Tag 099N(5)
(blueprint: def-pur-integral-derived-operations). -/
noncomputable def integralDerivedPullback {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) :
    DerivedCategory (integralTowerModules.{t, u} l E Y) ⥤
      DerivedCategory (integralTowerModules.{t, u} l E X) :=
  (integralPullbackDescent l E f).functor

/-- The defining natural comparison on all K-flat representatives with flat terms.
Together with this comparison, the descent is unique up to unique isomorphism.
Source: Bhatt--Scholze, Lemma 6.5.9(4); Stacks Project, Tag 099N(5)
(blueprint: def-pur-integral-derived-operations). -/
noncomputable def integralDerivedPullbackComparison {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) :
    integralOperationsGoodLocalization l E Y ⋙ integralDerivedPullback l E f ≅
      integralOperationsPullbackOnGood l E f :=
  (integralPullbackDescent l E f).comparison

/-- A completed tensor descent, its model comparison, and its universal property.
The record keeps the data together so consumers do not unfold nested existence proofs.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4)
(blueprint: def-pur-integral-derived-operations). -/
structure IntegralCompletedTensorDescent (W : AlgebraicGeometry.Scheme.{t}) where
  functor : (DerivedCategory (integralTowerModules l E W)) ×
    (DerivedCategory (integralTowerModules l E W)) ⥤
      DerivedCategory (integralTowerModules l E W)
  comparison : ((integralOperationsGoodLocalization l E W).prod
    (integralOperationsGoodLocalization l E W)) ⋙ functor ≅
      integralOperationsTensorOnGood l E W
  universal : ∀ (G' : (DerivedCategory (integralTowerModules l E W)) ×
      (DerivedCategory (integralTowerModules l E W)) ⥤
        DerivedCategory (integralTowerModules l E W))
    (d' : ((integralOperationsGoodLocalization l E W).prod
      (integralOperationsGoodLocalization l E W)) ⋙ G' ≅
        integralOperationsTensorOnGood l E W),
    ∃! ι : functor ≅ G', Functor.isoWhiskerLeft
      ((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ι ≪≫ d' = comparison

/-- The existing normalized descent, packaged without making a new choice.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4)
(blueprint: def-pur-integral-derived-operations). -/
noncomputable def integralCompletedTensorDescent (W : AlgebraicGeometry.Scheme.{t}) :
    IntegralCompletedTensorDescent l E W where
  functor :=
    (integralOperationsWellDefined l E (𝟙 W) W).2.2.choose_spec.choose_spec.choose
  comparison :=
    (integralOperationsWellDefined l E (𝟙 W) W).2.2.choose_spec.choose_spec.choose_spec.choose
  universal :=
    (integralOperationsWellDefined l E (𝟙 W) W).2.2.choose_spec.choose_spec
      |>.choose_spec.choose_spec.2.1

/-- The completed tensor product is the normalized descent of the Roos complex
of Res_n(P_n ⊗ Q_n), with the direct-sum total tensor differential and the
pure-tensor reduction transitions specified in IntegralOperationsWellDefined.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4)
(blueprint: def-pur-integral-derived-operations). -/
noncomputable def integralCompletedTensor (W : AlgebraicGeometry.Scheme.{t}) :
    (DerivedCategory (integralTowerModules.{t, u} l E W)) ×
      (DerivedCategory (integralTowerModules.{t, u} l E W)) ⥤
        DerivedCategory (integralTowerModules.{t, u} l E W) :=
  (integralCompletedTensorDescent l E W).functor

/-- The defining natural comparison with the finite-tensor Roos construction on
pairs of K-flat complexes with flat terms. The descent with this comparison
is unique up to unique compatible isomorphism.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4)
(blueprint: def-pur-integral-derived-operations). -/
noncomputable def integralCompletedTensorComparison (W : AlgebraicGeometry.Scheme.{t}) :
    ((integralOperationsGoodLocalization l E W).prod
      (integralOperationsGoodLocalization l E W)) ⋙ integralCompletedTensor l E W ≅
        integralOperationsTensorOnGood l E W :=
  (integralCompletedTensorDescent l E W).comparison

/-- Integral internal Hom is the ambient derived sheaf Hom over the actual
completed ring sheaf, computed by a K-injective resolution of its second argument
among all modules over that sheaf. It is contravariant in its first argument.
Source: Bhatt--Scholze, Lemma 3.4.11; Stacks Project, Section 08J7
(blueprint: def-pur-integral-derived-operations). -/
noncomputable def integralDerivedInternalHom (W : AlgebraicGeometry.Scheme.{t}) :
    (DerivedCategory (integralTowerModules.{t, u} l E W))ᵒᵖ ×
      DerivedCategory (integralTowerModules.{t, u} l E W) ⥤
        DerivedCategory (integralTowerModules.{t, u} l E W) :=
  CategoryTheory.derivedInternalHomOfUniverses.{t + 1, t, u}
    (AlgebraicGeometry.Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)

end WeilConjectures
