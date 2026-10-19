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

/-- Completed integral derived pullback: the normalized descent of
P ↦ Cone(1-s)[-1] on the strict tower Res_n f*(P_n), with n denoting exponent n+1.
Source: Bhatt--Scholze, Lemma 6.5.9(4); Stacks Project, Tag 099N(5)
(blueprint: def-pur-integral-derived-operations). -/
noncomputable def integralDerivedPullback {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) :
    DerivedCategory (integralTowerModules.{t, u} l E Y) ⥤
      DerivedCategory (integralTowerModules.{t, u} l E X) :=
  (integralOperationsWellDefined l E f X).2.2.choose

/-- The defining natural comparison on all K-flat representatives with flat terms.
Together with this comparison, the descent is unique up to unique isomorphism.
Source: Bhatt--Scholze, Lemma 6.5.9(4); Stacks Project, Tag 099N(5)
(blueprint: def-pur-integral-derived-operations). -/
noncomputable def integralDerivedPullbackComparison {X Y : AlgebraicGeometry.Scheme.{t}}
    (f : X ⟶ Y) :
    integralOperationsGoodLocalization l E Y ⋙ integralDerivedPullback l E f ≅
      integralOperationsPullbackOnGood l E f :=
  (integralOperationsWellDefined l E f X).2.2.choose_spec.choose

/-- The completed tensor product is the normalized descent of the Roos complex
of Res_n(P_n ⊗ Q_n), with the direct-sum total tensor differential and the
pure-tensor reduction transitions specified in IntegralOperationsWellDefined.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4)
(blueprint: def-pur-integral-derived-operations). -/
noncomputable def integralCompletedTensor (W : AlgebraicGeometry.Scheme.{t}) :
    (DerivedCategory (integralTowerModules.{t, u} l E W)) ×
      (DerivedCategory (integralTowerModules.{t, u} l E W)) ⥤
        DerivedCategory (integralTowerModules.{t, u} l E W) :=
  (integralOperationsWellDefined l E (𝟙 W) W).2.2.choose_spec.choose_spec.choose

/-- The defining natural comparison with the finite-tensor Roos construction on
pairs of K-flat complexes with flat terms. The descent with this comparison
is unique up to unique compatible isomorphism.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4)
(blueprint: def-pur-integral-derived-operations). -/
noncomputable def integralCompletedTensorComparison (W : AlgebraicGeometry.Scheme.{t}) :
    ((integralOperationsGoodLocalization l E W).prod
      (integralOperationsGoodLocalization l E W)) ⋙ integralCompletedTensor l E W ≅
        integralOperationsTensorOnGood l E W :=
  (integralOperationsWellDefined l E (𝟙 W) W).2.2.choose_spec.choose_spec.choose_spec.choose

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
